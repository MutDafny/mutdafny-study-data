// dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Requires.dfy

method Main()
{
  test0(10);
  test5(11);
  test6(12);
  test1();
  test2();
}

predicate valid(x: int)
  decreases x
{
  x > 0
}

function ref1(y: int): int
  requires valid(y)
  decreases y
{
  y - 1
}

lemma assumption1()
  ensures forall a: int, b: int {:trigger ref1(b), ref1(a)} {:trigger ref1(b), valid(a)} {:trigger ref1(a), valid(b)} {:trigger valid(b), valid(a)} :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b
{
}

method test0(a: int)
  decreases a
{
  if ref1.requires(a) {
    ghost var b := ref1(a);
  }
}

method test5(a: int)
  decreases a
{
  if valid(-a) {
    assert ref1.requires(a);
  }
}

method test6(a: int)
  decreases a
{
  if ref1.requires(a) {
    assert valid(a);
  }
}

method test1()
{
  if * {
    assert forall a: int, b: int {:trigger ref1(b), ref1(a)} {:trigger ref1(b), valid(a)} {:trigger ref1(a), valid(b)} {:trigger valid(b), valid(a)} :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
  } else {
    assert forall a: int, b: int {:trigger ref1(b), ref1(a)} {:trigger ref1(b), ref1.requires(a)} {:trigger ref1(a), ref1.requires(b)} {:trigger ref1.requires(b), ref1.requires(a)} :: ref1.requires(a) && ref1.requires(b) && ref1(a) == ref1(b) ==> a == b;
  }
}

function {:opaque} ref2(y: int): int
  requires valid(y)
  decreases y
{
  y - 1
}

lemma assumption2()
  ensures forall a: int, b: int {:trigger ref2(b), ref2(a)} {:trigger ref2(b), valid(a)} {:trigger ref2(a), valid(b)} {:trigger valid(b), valid(a)} :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b
{
  reveal ref2();
}

method test2()
{
  assumption2();
  if * {
    assert forall a: int, b: int {:trigger ref2(b), ref2(a)} {:trigger ref2(b), valid(a)} {:trigger ref2(a), valid(b)} {:trigger valid(b), valid(a)} :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
  } else {
    assert forall a: int, b: int {:trigger ref2(b), ref2(a)} {:trigger ref2(b), ref2.requires(a)} {:trigger ref2(a), ref2.requires(b)} {:trigger ref2.requires(b), ref2.requires(a)} :: ref2.requires(a) && ref2.requires(b) && ref2(a) == ref2(b) ==> a == b;
  }
}
