// laboratory_tmp_tmps8ws6mu2_dafny-tutorial_exercise9.dfy

function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
  decreases n
{
  var i: int := 0;
  b := 0;
  var c := 0;
  while i < n
    invariant 0 <= i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
    decreases n - i
  {
    b, c := c, c + b;
    i := i + 1;
  }
}
