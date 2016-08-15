package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/constant"
	"go/printer"
	"go/token"
	"go/types"
	"log"
	"os"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var debug bool

func init() {
	flag.Usage = usage
	flag.BoolVar(&debug, "debug", false, "print debugging information")
}

func main() {
	flag.Parse()
	if flag.NArg() == 0 {
		flag.Usage()
	}
	errors, err := check(flag.Args())
	if err != nil {
		log.Fatal(errors)
	}
	for _, e := range errors {
		fmt.Printf("%s: possible nil pointer dereference: %s\n", e.pos, e.expr)
	}
	if len(errors) != 0 {
		os.Exit(1)
	}
}

func usage() {
	fmt.Fprintf(os.Stderr, "Usage: %s [options] <args>\n", os.Args[0])
	fmt.Fprintln(os.Stderr, loader.FromArgsUsage)
	fmt.Fprintln(os.Stderr, "Options:")
	flag.PrintDefaults()
	os.Exit(2)
}

func check(args []string) ([]*npd, error) {
	var conf loader.Config
	_, err := conf.FromArgs(args, false)
	if err != nil {
		return nil, err
	}
	lprog, err := conf.Load()
	if err != nil {
		return nil, err
	}
	prog := ssautil.CreateProgram(lprog, ssa.BuilderMode(0))
	prog.Build()
	c := newChecker(prog, lprog)
	return c.check(), nil
}

type npd struct {
	pos  token.Position
	expr string
}

type checker struct {
	prog  *ssa.Program
	lprog *loader.Program
}

func newChecker(prog *ssa.Program, lprog *loader.Program) *checker {
	return &checker{prog, lprog}
}

func (c *checker) check() (errors []*npd) {
	for fn, _ := range ssautil.AllFunctions(c.prog) {
		DEBUGLN(fn, fn.Signature)
		for i, block := range fn.DomPreorder() {
			DEBUGF("%d:\n", i)
			for _, instr := range block.Instrs {
				DEBUGF("\t; %#v\n", instr)
				DEBUGF("\t")
				if v, ok := instr.(ssa.Value); ok {
					DEBUGF("%s = ", v.Name())
				}
				DEBUGLN(instr)
				DEBUGLN("\t\tunreachable:", unreachable(instr, nil))
				if v, ok := instr.(ssa.Value); ok {
					DEBUGLN("\t\tconst:", symev(v, nil))
				}
				if e := c.checkInstr(instr, nil); e != nil {
					errors = append(errors, e)
				}
			}
		}
		DEBUGLN()
		DEBUGLN()
	}
	return errors
}

func unreachable(instr ssa.Instruction, args map[*ssa.Parameter]ssa.Value) bool {
	idom := instr.Block().Idom()
	if idom == nil {
		// The entry and recover nodes do not have a parent
		// and are always reachable
		return false
	}
	ctrl := idom.Instrs[len(idom.Instrs)-1]
	if unreachable(ctrl, args) {
		return true
	}
	switch ctrl := ctrl.(type) {
	case *ssa.If:
		c := symev(ctrl.Cond, args)
		if c == nil {
			return false
		}
		var dst *ssa.BasicBlock
		if constant.BoolVal(c[0].(*ssa.Const).Value) {
			dst = ctrl.Block().Succs[0]
		} else {
			dst = ctrl.Block().Succs[1]
		}
		return dst != instr.Block()
	case *ssa.Jump:
		return ctrl.Block().Succs[0] != instr.Block()
	case *ssa.Panic, *ssa.Return:
		return true
	}
	return false
}

func allocType(a *ssa.Alloc) types.Type {
	return a.Type().Underlying().(*types.Pointer).Elem()
}

func symev(v ssa.Value, args map[*ssa.Parameter]ssa.Value) []ssa.Value {
	switch v := v.(type) {
	case *ssa.Alloc:
		return []ssa.Value{v}
	case *ssa.BinOp:
		x, y := symev(v.X, args), symev(v.Y, args)
		if x == nil || y == nil {
			break
		}
		var equal bool
		switch xx := x[0].(type) {
		case *ssa.Alloc:
			yy, ok := y[0].(*ssa.Alloc)
			if !ok {
				break
			}
			equal = types.Identical(allocType(xx), allocType(yy))
		case *ssa.Const:
			yy, ok := y[0].(*ssa.Const)
			if !ok {
				break
			}
			if !xx.IsNil() && !yy.IsNil() {
				return []ssa.Value{ssa.NewConst(constant.BinaryOp(xx.Value, v.Op, yy.Value), v.Type())}
			}
			switch v.Op {
			case token.EQL:
				equal = types.Identical(xx.Type(), yy.Type()) && xx.Value == yy.Value
			case token.NEQ:
				equal = types.Identical(xx.Type(), yy.Type()) || xx.Value != yy.Value
			default:
				panic("unreachable")
			}
		}
		return []ssa.Value{ssa.NewConst(constant.MakeBool(equal), v.Type())}
	case *ssa.Builtin:
	case *ssa.Call:
		// TODO: handle calls that cause side effects
		if v.Call.IsInvoke() { // call to an interface method
			break
		}
		switch fn := v.Call.Value.(type) {
		case *ssa.Function:
			params := mapParamsToArgs(fn.Params, v.Call.Args)
			return symev(fn, params)
		case *ssa.MakeClosure:
			params := mapParamsToArgs(fn.Fn.(*ssa.Function).Params, fn.Bindings)
			return symev(fn.Fn.(*ssa.Function), params)
		default:
			return symev(fn, args)
		}
	case *ssa.ChangeInterface:
		return symev(v.X, args)
	case *ssa.ChangeType:
		return symev(v.X, args)
	case *ssa.Const:
		return []ssa.Value{v}
	case *ssa.Convert:
		return symev(v.X, args)
	case *ssa.Extract:
		return []ssa.Value{symev(v.Tuple, args)[v.Index]}
	case *ssa.Function:
		if v.Blocks == nil { // external function: no source code
			break
		}
		var cur int
		for {
			block := v.Blocks[cur]
			if len(block.Instrs) == 0 {
				return nil // unreachable
			}
			switch ctrl := block.Instrs[len(block.Instrs)-1].(type) {
			case *ssa.If:
				cond := symev(ctrl.Cond, args)
				if cond == nil {
					return nil
				}
				if constant.BoolVal(cond[0].(*ssa.Const).Value) {
					cur = block.Succs[0].Index
				} else {
					cur = block.Succs[1].Index
				}
				continue
			case *ssa.Jump:
				cur = block.Succs[0].Index
				continue
			case *ssa.Panic:
				return nil
			case *ssa.Return:
				res := make([]ssa.Value, 0, len(ctrl.Results))
				allNil := true
				for _, r := range ctrl.Results {
					c := symev(r, args)
					if c == nil {
						res = append(res, nil)
						continue
					}
					res = append(res, c[0])
					allNil = false
				}
				if allNil {
					return nil
				}
				return res
			}
		}
	case *ssa.Global:
		return nil
	case *ssa.Parameter:
		return symev(args[v], nil)
	}
	return nil
}

func mapParamsToArgs(params []*ssa.Parameter, args []ssa.Value) map[*ssa.Parameter]ssa.Value {
	m := make(map[*ssa.Parameter]ssa.Value, len(args))
	for i, p := range params {
		m[p] = args[i]
	}
	return m
}

// checkInstr returns nil if instr can not cause a nil pointer dereference.
func (c *checker) checkInstr(instr ssa.Instruction, instrArgs map[*ssa.Parameter]ssa.Value) *npd {
	// TODO: perf: do this for each block instead
	if unreachable(instr, instrArgs) {
		return nil
	}
	var isnil bool
	switch instr := instr.(type) { // must match instrToNPD
	case *ssa.FieldAddr:
		DEBUGF("\t\tselected: %s ; %#v\n", instr.X, instr.X)
		isnil = isNil(instr.X, instrArgs)
		DEBUGLN("is nil:", isnil)
	case *ssa.Call:
		if instr.Call.IsInvoke() { // call to an interface method
			return nil
		}
		var callFn *ssa.Function
		var args []ssa.Value
		switch v := instr.Call.Value.(type) {
		case *ssa.Function:
			callFn = v
			args = instr.Call.Args
		case *ssa.MakeClosure:
			callFn = v.Fn.(*ssa.Function)
			args = v.Bindings
		}
		var nilArg bool
		for _, arg := range args {
			if isNil(arg, instrArgs) {
				nilArg = true
				break
			}
		}
		DEBUGLN("nilArg:", nilArg)
		DEBUGLN("callCausesNPD:", c.callCausesNPD(callFn, args))
		// FIXME: argument does not have to be nil to cause a nil pointer dereference
		isnil = nilArg && c.callCausesNPD(callFn, args)
	}
	if isnil {
		return instrToNPD(instr, c.lprog)
	}
	return nil
}

func (c *checker) callCausesNPD(fn *ssa.Function, args []ssa.Value) bool {
	params := make(map[*ssa.Parameter]ssa.Value, len(args))
	for i, p := range fn.Params {
		params[p] = args[i]
	}
	for _, block := range fn.DomPreorder() {
		for _, instr := range block.Instrs {
			if e := c.checkInstr(instr, params); e != nil {
				return true
			}
		}
	}
	return false
}

// isNil returns whether v may be nil.
func isNil(v ssa.Value, args map[*ssa.Parameter]ssa.Value) bool {
	if eval := symev(v, args); eval != nil {
		allAlloc := true
		for _, val := range eval {
			if _, ok := val.(*ssa.Alloc); !ok {
				allAlloc = false
				break
			}
		}
		if allAlloc {
			return false
		}
	}
	switch v := v.(type) {
	case *ssa.Alloc:
		return false
	case *ssa.Call:
		if v.Call.IsInvoke() { // call to an interface method
			return false
		}
		switch call := v.Call.Value.(type) {
		case *ssa.Builtin:
			return false
		case *ssa.Function:
			return callReturnsNil(call, v.Call.Args)
		case *ssa.MakeClosure:
			return callReturnsNil(call.Fn.(*ssa.Function), call.Bindings)
		default:
			return isNil(call, args)
		}
	case *ssa.Const:
		return v.IsNil()
	case *ssa.Global:
		return false
	case *ssa.Parameter:
		return isNil(args[v], nil)
	case *ssa.Phi:
		for _, e := range v.Edges {
			if isNil(e, nil) {
				return true
			}
		}
	}
	return false
}

func callReturnsNil(fn *ssa.Function, args []ssa.Value) bool {
	params := make(map[*ssa.Parameter]ssa.Value, len(args))
	for i, p := range fn.Params {
		params[p] = args[i]
	}
	for _, block := range fn.DomPreorder() {
		for _, instr := range block.Instrs {
			if ret, ok := instr.(*ssa.Return); ok {
				for _, res := range ret.Results {
					if isNil(res, params) {
						return true
					}
				}
			}
		}
	}
	return false
}

func findSelectorExpr(path []ast.Node) *ast.SelectorExpr {
	for _, n := range path {
		if sexpr, ok := n.(*ast.SelectorExpr); ok {
			return sexpr
		}
	}
	return nil
}

func instrToNPD(instr ssa.Instruction, lprog *loader.Program) *npd {
	// XXX: instr.Pos may return go/token.NoPos
	_, path, _ := lprog.PathEnclosingInterval(instr.Pos(), instr.Pos())
	var node ast.Node
	switch instr.(type) { // must match checker.checkInstr
	case *ssa.FieldAddr:
		node = findSelectorExpr(path).X
	default:
		node = path[0]
	}
	pos := lprog.Fset.Position(instr.Pos())
	src := nodeToString(node, lprog.Fset)
	return &npd{pos, src}
}

func nodeToString(n interface{}, fset *token.FileSet) string {
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, fset, n); err != nil {
		panic(err)
	}
	return buf.String()
}

func DEBUGF(format string, a ...interface{}) {
	if debug {
		fmt.Printf(format, a...)
	}
}

func DEBUGLN(a ...interface{}) {
	if debug {
		fmt.Println(a...)
	}
}
