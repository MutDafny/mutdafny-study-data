// dafny-workout_tmp_tmp0abkw6f8_starter_ex09.dfy

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
  var i: int := 1;
  if 0 <= n < 2 {
    return n;
  }
  b := 1;
  var c := 1;
  while i < n
    invariant 0 < i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
    decreases n - i
  {
    b, c := c, b + c;
    i := i + 1;
  }
}

method Main()
{
  var ret := ComputeFib(0);
  assert ret == fib(5);
}
