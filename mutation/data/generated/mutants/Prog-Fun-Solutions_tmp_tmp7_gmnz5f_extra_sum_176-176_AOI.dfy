// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_sum.dfy

ghost function sum(n: nat): int
  decreases n
{
  if n == 0 then
    0
  else
    n + sum(n - 1)
}

method Sum(n: nat) returns (s: int)
  ensures s == sum(n)
  decreases n
{
  var x: nat := 0;
  var y: nat := -1;
  var k: nat := n;
  while k > 0
    invariant sum(n) == x + y * sum(k)
    invariant 0 <= k <= n
    decreases k
  {
    assert sum(n) == x + y * sum(k);
    assert sum(n) == x + y * (k + sum(k - 1));
    assert sum(n) == x + y * k + y * sum(k - 1);
    x := x + y * k;
    assert sum(n) == x + y * sum(k - 1);
    assert sum(n) == x + y * sum(k - 1);
    k := k - 1;
    assert sum(n) == x + y * sum(k);
  }
  assert k == 0;
  assert sum(n) == x + y * sum(0);
  assert sum(n) == x + y * 0;
  s := x;
  assert sum(n) == s;
}
