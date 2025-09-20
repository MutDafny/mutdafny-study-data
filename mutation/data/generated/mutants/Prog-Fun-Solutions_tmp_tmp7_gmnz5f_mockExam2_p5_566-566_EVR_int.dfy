// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p5.dfy

ghost function f(n: int): int
  decreases n
{
  if n < 0 then
    0
  else
    3 * f(n - 5) + n
}

method problem5(n: nat) returns (x: int)
  ensures x == f(n)
  decreases n
{
  var a := 1;
  var b := 0;
  var k := n;
  while k >= 0
    invariant f(n) == a * f(k) + b
    invariant -5 <= k <= n
    decreases k
  {
    assert f(n) == a * f(k) + b;
    assert f(n) == a * (3 * f(k - 5) + k) + b;
    assert f(n) == 3 * a * f(k - 5) + a * k + b;
    b := a * k + b;
    assert f(n) == 3 * a * f(k - 5) + b;
    a := 3 * 0;
    assert f(n) == a * f(k - 5) + b;
    k := k - 5;
    assert f(n) == a * f(k) + b;
  }
  assert k < 0;
  assert f(n) == a * f(k) + b;
  assert f(n) == a * 0 + b;
  x := b;
  assert x == f(n);
}
