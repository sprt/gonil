package pkg

type A struct {
	X int
}

func ayy() {
	a := &A{X: 5}
	_ = a.X
}

func npd() {
	var a *A
	_ = a.X         // MATCH a
	_ = (*A)(nil).X // MATCH (*A)(nil)
}

func noNPD() {
	a := new(A)
	_ = a.X
	b := &A{}
	_ = b.X
	c := A{}
	_ = c.X
}

func canReturnNil(ok bool) *A {
	if ok {
		return new(A)
	}
	return nil
}

func npdInterProc() {
	a := canReturnNil(true)
	_ = a.X
}

func npdGuarded() {
	a := canReturnNil(false)
	if a == nil {
		return
	}
	_ = a.X
}

func npdNilArg() {
	expectNonNilParam := func(a *A) {
		_ = a.X
	}
	expectNonNilParam(nil) // MATCH expectNonNilParam(nil)
}
