// dafny-programs_tmp_tmpcwodh6qh_src_max.dfy

method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
  decreases a, b
{
  if a > b {
    return a;
  } else {
    return b;
  }
}

method MaxTest()
{
  var low := 0;
  var high := 10;
  var v := Max(low, high);
  assert v == high;
}

function max(a: int, b: int): int
  decreases a, b
{
  if a > b then
    a
  else
    b
}

method maxTest()
{
  assert max(1, 10) == 10;
}
