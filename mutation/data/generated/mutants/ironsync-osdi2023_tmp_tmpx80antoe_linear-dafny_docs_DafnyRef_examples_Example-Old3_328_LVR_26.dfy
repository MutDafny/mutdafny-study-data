// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old3.dfy

class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    requires z1.Length > 10 && z1[0] == 7
    requires z2.Length > 10 && z2[0] == 17
    modifies z2
  {
    var a: array<nat> := z1;
    assert a[0] == 7;
    a := z2;
    assert a[0] == 17;
    assert old(a[0]) == 17;
    z2[0] := 26;
    assert old(a[0]) == 17;
    assert old(a)[0] == 27;
  }
}
