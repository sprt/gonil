package pkg

type A struct {
	X int
}

func npd() {
	var a *A
	_ = a.X         // MATCH a
	_ = (*A)(nil).X // MATCH (*A)(nil)
}

func canReturnNil(ok bool) *A {
	if ok {
		return new(A)
	}
	return nil
}

func npdInterProc() {
	a := canReturnNil(true)
	_ = a.X // MATCH a
}

//func npdChecked() {
//        var a *A
//        if a == nil {
//                return
//        }
//        _ = a.X
//}

func npdNilArg() {
	expectNonNilParam := func(a *A) {
		_ = a.X
	}
	expectNonNilParam(nil) // MATCH expectNonNilParam(nil)
}
