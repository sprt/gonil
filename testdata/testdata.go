package pkg

type A struct {
	X int
	a *A
}

func npd() {
	_ = (*A)(nil).X   // MATCH (*A)(nil).X
	_ = (*A)(nil).a.X // MATCH (*A)(nil).a
	_ = new(A).X
	//_ = new(A).a.X // MATCH new(A).a.X
	_ = (&A{}).X
	_ = A{}.X
}

func canReturnNil(ok bool) *A {
	if ok {
		return new(A)
	}
	return nil
}

func expectNonNilParam(a *A) {
	_ = a.X
}

func interproc() {
	a := canReturnNil(true)
	_ = a.X
}

func guarded() {
	a := canReturnNil(false)
	if a != nil {
		_ = a.X
	}
	if a == nil {
		return
	}
	_ = a.X
}

func nilArg() {
	expectNonNilParam(nil) // MATCH expectNonNilParam(nil)
}
