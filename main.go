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

type npd struct {
	pos  token.Position
	expr string
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

	var errors []*npd
	for fn, _ := range ssautil.AllFunctions(prog) {
		debugln(fn, fn.Signature)
		for i, block := range fn.DomPreorder() {
			debugf("%d:\n", i)
			for _, instr := range block.Instrs {
				debugf("\t")
				if v, ok := instr.(ssa.Value); ok {
					debugf("%s = ", v.Name())
				}
				debugf("%s\t%#v\n", instr, instr)
				// TODO: inspect all function calls with potentially nil arguments
				if fieldAddr, ok := instr.(*ssa.FieldAddr); ok {
					debugf("---\t\t%s\t%#v\n", fieldAddr.X, fieldAddr.X)
					isnil := isNil(fieldAddr.X, nil)
					debugln("is nil:", isnil)
					if isnil {
						// XXX: fieldAddr.Pos may return go/token.NoPos
						_, path, _ := lprog.PathEnclosingInterval(fieldAddr.Pos(), fieldAddr.Pos())
						sexpr := findSelectorExpr(path)
						expr := nodeToString(sexpr.X, prog.Fset)
						debugln(expr)
						pos := prog.Fset.Position(fieldAddr.Pos())
						debugln("pos:", fieldAddr.Pos().IsValid(), pos)
						errors = append(errors, &npd{pos, expr})
					}
				}
			}
		}
		debugln()
		debugln()
	}
	return errors, nil
}

func isNil(v ssa.Value, args map[*ssa.Parameter]ssa.Value) bool {
	switch v := v.(type) {
	case *ssa.Alloc:
		return v.Comment == "new"
	case *ssa.Call:
		if v.Call.IsInvoke() {
			return false
		}
		switch call := v.Call.Value.(type) {
		case *ssa.Builtin:
			return false
		case *ssa.Function:
			return isNilCall(call, v.Call.Args)
		case *ssa.MakeClosure:
			return isNilCall(call.Fn.(*ssa.Function), call.Bindings)
		default:
			return isNil(call, nil)
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

func isNilCall(fn *ssa.Function, args []ssa.Value) bool {
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
