package main

import (
	"go/parser"
	"go/token"
	"strings"
	"testing"
)

func TestMain(t *testing.T) {
	const testFile = "testdata/testdata.go"
	instrs := parseInstructions(t, testFile)
	traces, err := check([]string{testFile})
	if err != nil {
		t.Fatal(err)
	}
outer:
	for _, instr := range instrs {
		for i, tr := range traces {
			npd := tr[0]
			if npd.src() == instr.src && npd.pos().Line == instr.pos.Line {
				traces = append(traces[:i], traces[i+1:]...)
				continue outer
			}
		}
		t.Errorf("%s: did not match: %s", instr.pos, instr.src)
	}
	for _, tr := range traces {
		npd := tr[0]
		t.Errorf("%s: unexpected match: %s", npd.pos(), npd.src())
	}
}

type pinstruction struct {
	pos token.Position
	src string
}

func parseInstructions(t *testing.T, filename string) []*pinstruction {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, filename, nil, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	var instrs []*pinstruction
	for _, cg := range f.Comments {
		text := cg.Text()
		expr := strings.TrimPrefix(text, "MATCH ")
		if expr != text {
			pos := fset.Position(cg.Pos())
			instrs = append(instrs, &pinstruction{pos, strings.TrimSpace(expr)})
		}
	}
	return instrs
}
