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
  }
}
