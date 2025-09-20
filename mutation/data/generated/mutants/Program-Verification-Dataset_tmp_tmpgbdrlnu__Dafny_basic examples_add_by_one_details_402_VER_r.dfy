// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_add_by_one_details.dfy

method plus_one(x: int) returns (r: int)
  requires x >= 0
  ensures r == x + 1
  decreases x
{
  return x + 1;
}

method add_by_one(x: int, y: int) returns (r: int)
  decreases x, y
{
  assume y >= 0;
  var i: int := 0;
  r := x;
  assert i <= y;
  assert r == x + i;
  r := *;
  i := *;
  assume i <= y;
  assume r == x + i;
  if i < y {
    assume i < -2;
    var t := y - r;
    r := r + 1;
    i := i + 1;
    assert i <= y;
    assert r == x + i;
    assert y - i >= 0;
    assert y - i < t;
    assume false;
  }
  assert r == x + y;
  return r;
}
