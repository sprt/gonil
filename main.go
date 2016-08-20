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
	"io/ioutil"
	"log"
	"os"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var debug bool

func init() {
	log.SetFlags(0)
	log.SetOutput(ioutil.Discard)
	flag.Usage = usage
	flag.BoolVar(&debug, "debug", false, "print debugging information")
}

func main() {
	flag.Parse()
	if flag.NArg() == 0 {
		flag.Usage()
	}
	if debug {
		log.SetOutput(os.Stderr)
	}
	traces, err := check(flag.Args())
	if err != nil {
		fmt.Fprint(os.Stderr, err)
		os.Exit(2)
	}
	for _, tr := range traces {
		for i, instr := range tr {
			if i != 0 {
				fmt.Print("\t")
			}
			fmt.Printf("%s: possible nil pointer dereference: %s\n", instr.pos(), instr.src())
		}
	}
	if len(traces) != 0 {
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

func check(args []string) ([]trace, error) {
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
	c := &checker{lprog: lprog}
	fr := &frame{checker: c}
	for fn := range ssautil.AllFunctions(prog) {
		_ = fr.symEvalFunc(nil, fn, nil, 0)
	}
	return c.npds, nil
}

type checker struct {
	lprog *loader.Program
	npds  []trace
}

func (c *checker) report(instr ssa.Instruction, fr *frame) {
	c.npds = append(c.npds, append(fr.tr, &instruction{instr, c.lprog}))
}

type instruction struct {
	ssa.Instruction
	lprog *loader.Program
}

func (instr *instruction) pos() token.Position {
	return instr.lprog.Fset.Position(instr.Pos())
}

func (instr *instruction) src() string {
	_, path, _ := instr.lprog.PathEnclosingInterval(instr.Pos(), instr.Pos())
	var node ast.Node
	switch instr.Instruction.(type) {
	case *ssa.FieldAddr:
		node = findSelectorExpr(path)
	default:
		node = path[0]
	}
	var buf bytes.Buffer
	printer.Fprint(&buf, instr.lprog.Fset, node)
	return buf.String()
}

type trace []*instruction

type value struct {
	val  ssa.Value
	zero bool
}

type phi []*value

type frame struct {
	fn      *ssa.Function
	args    []ssa.Value
	tr      trace
	checker *checker
}

func (fr *frame) report(instr ssa.Instruction) {
	fr.checker.report(instr, fr)
}

func (fr *frame) symEval(v *value) phi {
	switch v := v.val.(type) {
	case *ssa.Alloc:
		var zero bool
		switch goType(v.Type()).(type) {
		case *types.Chan, *types.Map, *types.Slice:
			zero = true
		}
		return []*value{{v, zero}}
	case *ssa.BinOp:
		xx, yy := fr.symEval(&value{val: v.X}), fr.symEval(&value{val: v.Y})
		edges := make(phi, 0, len(xx))
		for i, x := range xx {
			y := yy[i]
			c := ssa.NewConst(nil, v.Type())
			switch v.Op {
			case token.ADD, token.SUB:
				addEdge(&edges, c, x.zero && y.zero)
			case token.MUL:
				addEdge(&edges, c, x.zero || y.zero)
			case token.QUO, token.REM:
				addEdge(&edges, c, x.zero)

			case token.AND, token.OR, token.XOR, token.AND_NOT:
				addEdge(&edges, c, x.zero && y.zero)
			case token.SHL, token.SHR:
				addEdge(&edges, c, x.zero)

			case token.EQL, token.LEQ, token.GEQ:
				switch {
				case x.zero && y.zero:
					edges = append(edges, &value{c, false})
				case x.zero != y.zero:
					edges = append(edges, &value{c, true})
				default: // !x.zero && !y.zero
					edges = append(edges, &value{c, false})
					edges = append(edges, &value{c, true})
				}
			case token.NEQ:
				switch {
				case x.zero && y.zero:
					edges = append(edges, &value{c, true})
				case x.zero != y.zero:
					edges = append(edges, &value{c, false})
				default: // !x.zero && !y.zero
					edges = append(edges, &value{c, false})
					edges = append(edges, &value{c, true})
				}
			case token.LSS, token.GTR:
				// TODO: we can be more accurate here;
				// strings come to mind.
				edges = append(edges, &value{c, false})
				edges = append(edges, &value{c, true})
			}
		}
		return edges
	case *ssa.Call:
		return fr.symEvalCall(v, 0)
	case *ssa.Const:
		if v.IsNil() {
			return []*value{{v, true}}
		}
		var zero bool
		switch v.Value.Kind() {
		case constant.Bool:
			zero = !constant.BoolVal(v.Value)
		case constant.Complex:
			zero = v.Complex128() == 0
		case constant.Float:
			zero = v.Float64() == 0
		case constant.Int:
			zero = v.Uint64() == 0
		case constant.String:
			zero = constant.StringVal(v.Value) == ""
		}
		return []*value{{zero: zero}}
	case *ssa.Extract:
		return fr.symEvalExtract(v)
	case *ssa.FieldAddr:
		xx := fr.symEval(&value{val: v.X})
		if xx == nil {
			return nil
		}
		edges := make(phi, 0, 2*len(xx))
		for _, x := range xx {
			if _, ok := x.val.(*ssa.Const); /*x.zero ||*/ ok {
				// Constant *struct is always (*struct)(nil)
				fr.report(v)
				break
			}
			field := goType(x.val.Type()).(*types.Struct).Field(v.Field)
			c := ssa.NewConst(nil, named(field.Type()))
			edges = append(edges, &value{c, true})
			if !x.zero {
				edges = append(edges, &value{c, false})
			}
		}
		return edges
	case *ssa.Global:
		return nil
	case *ssa.Lookup:
		// val.CommaOk == false
		xx := fr.symEval(&value{val: v.X})
		if xx == nil {
			return nil
		}
		if _, ok := xx[0].val.Type().(*types.Map); !ok {
			// Possible index out of range error
			// (guaranteed if x.zero)
			return nil
		}
		edges := make(phi, 0, len(xx))
		for _, x := range xx {
			c := ssa.NewConst(nil, x.val.Type().(*types.Map).Elem())
			edges = append(edges, &value{c, true})
			if !x.zero {
				edges = append(edges, &value{c, false})
			}
		}
		return edges
	case *ssa.Next, *ssa.TypeAssert:
		panic("unreachable") // handled by symEvalExtract
	case *ssa.Parameter:
		if fr.args == nil {
			return nil
		}
		var arg ssa.Value
		for i, p := range fr.fn.Params {
			if p == v {
				arg = fr.args[i]
				break
			}
		}
		return fr.symEval(&value{val: arg})
	//case *ssa.UnOp:
	//        // FIXME
	//        return fr.symEval(&value{val: v.X})
	default:
		return nil
	}
}

func (fr *frame) symEvalExtract(t *ssa.Extract) phi {
	switch val := t.Tuple.(type) {
	case *ssa.Call:
		return fr.symEvalCall(val, t.Index)
	case *ssa.Lookup:
		// val.X is a map
		xx := fr.symEval(&value{val: val.X})
		if xx == nil {
			return nil
		}
		edges := make(phi, 0, len(xx))
		for _, x := range xx {
			// If x.zero, x[k] is zero;
			// otherwise it can also be non-zero.
			var typ types.Type
			if t.Index == 0 { // x[k]
				typ = x.val.Type().(*types.Map).Elem()
				edges = append(edges, &value{ssa.NewConst(nil, typ), true})
			} else { // ,ok
				typ = types.Typ[types.Bool]
				edges = append(edges, &value{ssa.NewConst(nil, typ), true})
			}
			if !x.zero {
				edges = append(edges, &value{ssa.NewConst(nil, typ), false})
			}
		}
		return edges
	default:
		// TODO?
		return nil
	}
}

func (fr *frame) symEvalCall(call ssa.CallInstruction, res int) phi {
	if call.Common().IsInvoke() {
		return nil // call to an interface method
	}
	switch f := call.Common().Value.(type) {
	case *ssa.Function:
		return fr.symEvalFunc(call, f, call.Common().Args, res)
	case *ssa.MakeClosure:
		return fr.symEvalFunc(call, f.Fn.(*ssa.Function), f.Bindings, res)
	default:
		return fr.symEval(&value{val: f})
	}
}

func (fr *frame) symEvalFunc(call ssa.CallInstruction, fn *ssa.Function, args []ssa.Value, res int) phi {
	if fn.Blocks == nil {
		return nil // external function: no source code available
	}
	tr := fr.tr
	if call != nil {
		tr = append(tr, &instruction{call, fr.checker.lprog})
	}
	newfr := &frame{fn, args, tr, fr.checker}
	return newfr.symEvalBlock(fn.Blocks[0], res)
}

func (fr *frame) symEvalBlock(block *ssa.BasicBlock, res int) phi {
	if len(block.Instrs) == 0 {
		return nil // block is unreachable
	}
	for _, instr := range block.Instrs {
		//log.Printf("\t; %#v", instr)
		//var pre string
		//var edges phi
		if v, ok := instr.(ssa.Value); ok {
			if debug {
				//pre = v.Name() + " = "
				//edges = fr.symEval(&value{val: v})
			}
			switch v := v.(type) {
			case *ssa.FieldAddr:
				_ = fr.symEval(&value{val: v})
			case *ssa.Call:
				// XXX: only check calls where we're passing pointers?
				var f *ssa.Function
				var args []ssa.Value
				switch call := v.Call.Value.(type) {
				case *ssa.Function:
					f = call
					args = v.Call.Args
				case *ssa.MakeClosure:
					f = call.Fn.(*ssa.Function)
					args = call.Bindings
				}
				if f != nil {
					_ = fr.symEvalFunc(v, f, args, 0)
				}
			}
		}
		//for i, val := range edges {
		//        log.Printf("\t; %d=%#v", i, val)
		//}
		//log.Print("\t", pre, instr)
		//log.Print("\n")
	}
	switch ctrl := block.Instrs[len(block.Instrs)-1].(type) {
	case *ssa.If:
		cond := fr.symEval(&value{val: ctrl.Cond})
		if cond == nil {
			return nil
		}
		edges := make(phi, 0, len(cond))
		tru, fals := false, false
		for _, c := range cond {
			if c.zero {
				fals = true
			} else {
				tru = true
			}
		}
		if tru {
			edges = append(edges, fr.symEvalBlock(block.Succs[0], res)...)
		}
		if fals {
			edges = append(edges, fr.symEvalBlock(block.Succs[1], res)...)
		}
		return edges
	case *ssa.Jump:
		return fr.symEvalBlock(block.Succs[0], res)
	case *ssa.Panic:
		return nil
	case *ssa.Return:
		if len(ctrl.Results) == 0 {
			return nil
		}
		return fr.symEval(&value{val: ctrl.Results[res]})
	default:
		panic("unreachable")
	}
}

func addEdge(edges *phi, v ssa.Value, guaranteedZero bool) {
	if !guaranteedZero {
		*edges = append(*edges, &value{v, false})
	}
	*edges = append(*edges, &value{v, true})
}

func named(typ types.Type) types.Type {
	if _, ok := typ.(*types.Named); ok {
		return named(typ.Underlying())
	}
	return typ
}

func goType(typ types.Type) types.Type {
	if _, ok := typ.(*types.Named); ok {
		return goType(typ.Underlying())
	}
	if p, ok := typ.Underlying().(*types.Pointer); ok {
		return goType(p.Elem())
	}
	return typ
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
