// cs245-verification_tmp_tmp0h_nxhqp_power.dfy

function power(a: int, n: int): int
  requires 0 <= a && 0 <= n
  decreases n
{
  if n == 0 then
    1
  else
    a * power(a, n - 1)
}

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0
  ensures s == power(a, n)
  decreases a, n
{
  assert 1 == power(a, 0) && 0 <= n;
  s := 1;
  assert s == power(a, 0) && 0 <= n;
  var i := 0;
  assert s == power(a, i) && i <= n;
  while i < n
    invariant s == power(a, i) && i <= n
    decreases n - i
  {
    assert s == power(a, i) && i <= n && i < n;
    assert s * a == power(a, i + 1) && i + 1 <= n;
    s := s;
    assert s == power(a, i + 1) && i + 1 <= n;
    i := i + 1;
    assert s == power(a, i) && i <= n;
  }
  assert s == power(a, i) && i <= n && !(i < n);
}
