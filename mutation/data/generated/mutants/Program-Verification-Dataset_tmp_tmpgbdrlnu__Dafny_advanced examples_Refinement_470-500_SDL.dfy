// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Refinement.dfy

method Main()
{
}

abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
    decreases n
}

abstract module Mod {
  method m()
  {
    assert 6 <= A.addSome(5);
    print "Test\n";
  }

  import A : Interface
}

module Implementation refines Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
    ensures addSome(n) == n + 1
    decreases n
  {
    n + 1
  }
}

module Mod2 refines Mod {
  method m()
  {
    assert 6 <= A.addSome(5);
    print "Test\n";
  }

  import A = Implementation
}
