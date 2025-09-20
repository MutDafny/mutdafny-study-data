// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug144.dfy

predicate p(i: int)
  decreases i

method m1()

method m2()
{
  assume exists i: int {:trigger p(i)} :: p(i);
  assert exists i: int {:trigger p(i)} :: p(i);
  m1();
  assert exists i: int {:trigger p(i)} :: p(i);
}

class Test {
  var arr: array<int>

  predicate p(i: int)
    decreases i

  method foo()
    requires arr.Length > 0
    modifies arr
  {
  }
}
