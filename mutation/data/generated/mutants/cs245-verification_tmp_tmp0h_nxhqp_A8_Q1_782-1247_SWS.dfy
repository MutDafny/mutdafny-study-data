// cs245-verification_tmp_tmp0h_nxhqp_A8_Q1.dfy

function power(a: int, n: int): int
  requires 0 <= n
  decreases n
{
  if n == 0 then
    1
  else
    a * power(a, n - 1)
}

method A8Q1(y0: int, x: int) returns (z: int)
  requires y0 >= 0
  ensures z == power(x, y0)
  decreases y0, x
{
  var y := y0;
  while y > 0
    invariant z == power(x, y0 - y) && y >= 0
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
  z := 1;
}
