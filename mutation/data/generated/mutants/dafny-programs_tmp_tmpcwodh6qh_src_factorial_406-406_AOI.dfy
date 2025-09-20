// dafny-programs_tmp_tmpcwodh6qh_src_factorial.dfy

function fact(n: nat): nat
  ensures fact(n) >= 1
  decreases n
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

method factorial(n: nat) returns (res: nat)
  ensures res == fact(n)
  decreases n
{
  var i := 1;
  res := 1;
  while i < n + 1
    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
    decreases n + 1 - i
  {
    res := i * -res;
    i := i + 1;
  }
}
