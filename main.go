package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
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
		debugln(fn, fn.Signature)
		for i, block := range fn.DomPreorder() {
			debugf("%d:\n", i)
			for _, instr := range block.Instrs {
				debugf("\t")
				if v, ok := instr.(ssa.Value); ok {
					debugf("%s = ", v.Name())
				}
				if e := c.checkInstr(instr, nil); e != nil {
					errors = append(errors, e)
				}
				debugf("%s\t%#v\n", instr, instr)
			}
		}
		debugln()
		debugln()
	}
	return errors
}

func (c *checker) checkInstr(instr ssa.Instruction, instrArgs map[*ssa.Parameter]ssa.Value) *npd {
	switch instr := instr.(type) {
	case *ssa.FieldAddr:
		debugf("---\t\t%s\t%#v\n", instr.X, instr.X)
		isnil := isNil(instr.X, instrArgs)
		debugln("is nil:", isnil)
		if isnil {
			// XXX: instr.Pos may return go/token.NoPos
			_, path, _ := c.lprog.PathEnclosingInterval(instr.Pos(), instr.Pos())
			sexpr := findSelectorExpr(path)
			expr := nodeToString(sexpr.X, c.prog.Fset)
			debugln("expr:", expr)
			pos := c.prog.Fset.Position(instr.Pos())
			debugln("pos:", instr.Pos().IsValid(), pos)
			return &npd{pos, expr}
		}
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
		debugln("nilArg:", nilArg)
		debugln("callCausesNPD:", c.callCausesNPD(callFn, args))
		if !nilArg || !c.callCausesNPD(callFn, args) {
			return nil
		}
		pos := c.prog.Fset.Position(instr.Pos())
		_, path, _ := c.lprog.PathEnclosingInterval(instr.Pos(), instr.Pos())
		expr := nodeToString(path[0], c.prog.Fset)
		return &npd{pos, expr}
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

func isNil(v ssa.Value, args map[*ssa.Parameter]ssa.Value) bool {
	switch v := v.(type) {
	case *ssa.Alloc:
		return v.Comment == "new"
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

func nodeToString(n interface{}, fset *token.FileSet) string {
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, fset, n); err != nil {
		panic(err)
	}
	return buf.String()
}

func debugf(format string, a ...interface{}) {
	if debug {
		fmt.Printf(format, a...)
	}
}

func debugln(a ...interface{}) {
	if debug {
		fmt.Println(a...)
	}
}
