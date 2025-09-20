// Dafny_Programs_tmp_tmp99966ew4_mymax.dfy

method Max(a: int, b: int) returns (c: int)
  ensures c >= a && c >= b
  decreases a, b
{
  if a < b {
    c := b;
  }
  assert a <= c && b <= c;
}

method Testing()
{
  var v := Max(2, 3);
  assert v >= 3;
}
