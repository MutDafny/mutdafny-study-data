// DafnyProjects_tmp_tmp2acw_s4s_sqrt.dfy

method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
  decreases x

method testSqrt()
{
  var r := sqrt(4.0);
  if r < 2.0 {
    monotonicSquare(-r, 2.0);
  }
  assert r == 2.0;
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
  decreases c, x, y
{
}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
  decreases x, y
{
  monotonicMult(x, x, y);
}
