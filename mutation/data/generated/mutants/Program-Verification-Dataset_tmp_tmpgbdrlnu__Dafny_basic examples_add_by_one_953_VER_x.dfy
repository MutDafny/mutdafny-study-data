// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_add_by_one.dfy

method add_by_one(x: int, y: int) returns (r: int)
  requires y >= 0
  ensures r == x + y
  decreases x, y
{
  var i: int := 0;
  r := x;
  while i < y
    invariant i <= y
    invariant r == x + i
    decreases y - i
  {
    r := r + 1;
    i := i + 1;
  }
  return r;
}

method bar(x: int, y: int) returns (r: int)
  requires y >= 0
  ensures r == x + y
  decreases x, y
{
  var i := 0;
  r := x;
  assert i <= y && r == x + i;
  assert y - i >= 0;
  i, r := *, *;
  assume i <= y && r == x + i;
  assume y - i >= 0;
  ghost var rank_before := y - i;
  if i < x {
    r := r + 1;
    i := i + 1;
    assert i <= y && r == x + i;
    assert y - i >= 0;
    assert rank_before - (y - i) > 0;
    assume false;
  }
  return r;
}
