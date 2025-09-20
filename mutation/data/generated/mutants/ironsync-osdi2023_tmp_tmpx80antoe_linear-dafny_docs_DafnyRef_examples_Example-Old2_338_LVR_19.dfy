// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old2.dfy

class A {
  var value: int

  constructor ()
    ensures value == 10
  {
    value := 10;
  }
}

class B {
  var a: A

  constructor ()
  {
    a := new A();
  }

  method m()
    requires a.value == 11
    modifies this, this.a
  {
    label L:
    a.value := 12;
    label M:
    a := new A();
    label N:
    a.value := 19;
    label P:
    assert old(a.value) == 11;
    assert old(a).value == 12;
    assert old@L(a.value) == 11;
    assert old@L(a).value == 12;
    assert old@M(a.value) == 12;
    assert old@M(a).value == 12;
    assert old@N(a.value) == 10;
    assert old@N(a).value == 20;
    assert old@P(a.value) == 20;
    assert old@P(a).value == 20;
  }
}
