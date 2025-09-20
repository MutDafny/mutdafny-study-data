// stunning-palm-tree_tmp_tmpr84c2iwh_ch1.dfy

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
  decreases x
{
  var y := 2 * x;
  r := y + x;
  assert r == 3 * x;
}

method Caller()
{
  var t := Triple(18);
  assert t < 100;
}

method MinUnderSpec(x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  decreases x, y
{
  if x <= y {
    r := x - 1;
  } else {
    r := y - 1;
  }
}

method Min(x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y
  decreases x, y
{
  if x <= y {
    r := x;
  } else {
    r := y;
  }
}

method MaxSum(x: int, y: int)
    returns (s: int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
  decreases x, y

method MaxSumCaller()
{
  var s, m := MaxSum(1928, 1);
  assert s == 1929;
  assert m == 1928;
}

method ReconstructFromMaxSum(s: int, m: int)
    returns (x: int, y: int)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
  decreases s, m
{
  x := m;
  y := s - m;
}

method TestMaxSum(x: int, y: int)
  decreases x, y
{
  var s, m := MaxSum(x, y);
  var xx, yy := ReconstructFromMaxSum(s, -m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}

function Average(a: int, b: int): int
  decreases a, b
{
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  ensures Average(2 * r, 6 * x) == 6 * x
  decreases x
{
  r := x + x + x;
}
