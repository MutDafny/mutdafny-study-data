// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny0_ModulePrint.dfy

method Main()
{
}

abstract module S {
  class C {
    var f: int
    ghost var g: int
    var h: int

    method m()
      modifies this
  }
}

module T refines S {
  class C ... {
    ghost var h: int
    ghost var j: int
    var k: int

    constructor ()
    {
    }

    method m()
      modifies this
      ensures h == h
      ensures j == j
    {
      assert k == k;
    }

    var f: int
    ghost var g: int
  }
}
