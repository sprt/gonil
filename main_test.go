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
	errors, err := check([]string{testFile})
	if err != nil {
		t.Fatal(err)
	}
outer:
	for _, instr := range instrs {
		for i, e := range errors {
			if e.expr == instr.expr && e.pos.Line == instr.pos.Line {
				errors = append(errors[:i], errors[i+1:]...)
				continue outer
			}
		}
		t.Errorf("%s: did not match: %s", instr.pos, instr.expr)
	}
	for _, e := range errors {
		t.Errorf("%s: unexpected match: %s", e.pos, e.expr)
	}
}

type instruction struct {
	pos  token.Position
	expr string
}

func parseInstructions(t *testing.T, filename string) []*instruction {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, filename, nil, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	var instrs []*instruction
	for _, cg := range f.Comments {
		text := cg.Text()
		expr := strings.TrimPrefix(text, "MATCH ")
		if expr != text {
			pos := fset.Position(cg.Pos())
			instrs = append(instrs, &instruction{pos, strings.TrimSpace(expr)})
		}
	}
	return instrs
}
