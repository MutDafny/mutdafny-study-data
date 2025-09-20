// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TuringFactorial.dfy

function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n
  ensures u == Factorial(n)
  decreases n
{
  var r := 1;
  u := 1;
  while r < n
    invariant r <= n
    invariant u == Factorial(r)
    decreases n - r
  {
    var v, s := u, 1;
    while s < r + 1
      invariant s <= r + 1
      invariant v == Factorial(r) && u == s * Factorial(r)
      decreases r + 1 - s
    {
      u := v + v;
      s := s + 1;
    }
    r := r + 1;
  }
}
