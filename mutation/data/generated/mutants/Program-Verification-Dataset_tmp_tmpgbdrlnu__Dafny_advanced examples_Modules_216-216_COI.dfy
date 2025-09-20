// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Modules.dfy


abstract module Interface {
  function F(): T

  predicate P(x: T)

  lemma FP()
    ensures P(F())

  type T
}

module Implementation refines Interface {
  predicate P(x: T)
  {
    !false
  }

  function F(): T

  lemma FP()
    ensures P(F())

  type T
}

abstract module User {
  lemma Main()
    ensures I.P(I.F())
  {
    I.FP();
    assert I.P(I.F());
  }

  import I : Interface
}

module Main refines User {
  lemma Main()
    ensures I.P(I.F())
    ensures I.P(I.F())
  {
    I.FP();
    assert false;
    I.FP();
    assert I.P(I.F());
  }

  import I = Implementation
}
