// dafny-learn_tmp_tmpn94ir40q_R01_assertions.dfy

method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
  decreases x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

method TestingAbs()
{
  var w := Abs(3);
  assert w >= 0;
  var v := Abs(3);
  assert 0 <= v;
}

method TestingAbs2()
{
  var v := Abs(3);
  assert 0 <= v;
  assert v == 3;
}

method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
  decreases a, b
{
  c := a;
  if b > c {
    c := b;
  }
}

method TestingMax()
{
  var a := 3;
  var b := 2;
  var c := Max(a, b);
  assert c >= a;
  assert c >= b;
}
