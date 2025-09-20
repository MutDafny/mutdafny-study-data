// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old.dfy

class A {
  var value: int

  method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
    decreases i
  {
    value := 43;
    var j: int := 17;
    label L:
    j := 18;
    value := 44;
    label M:
    assert old(i) == 6;
    assert old(j) == 18;
    assert old@L(j) == 18;
    assert old(value) == 42;
    assert old@L(value) == 43;
    assert old@M(value) == 44 && this.value == 44;
  }
}
