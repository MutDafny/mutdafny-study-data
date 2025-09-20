// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseFibonacci.dfy

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

method fibonacci1(n: nat) returns (f: nat)
  ensures f == fib(n)
  decreases n
{
  var i := 0;
  f := 0;
  var fsig := 1;
  while i < n
    invariant f == fib(i) && fsig == fib(i + 1)
    invariant i <= n
    decreases n - i
  {
    f, fsig := fsig, f + fsig;
    i := i + 1;
  }
}

method fibonacci2(n: nat) returns (f: nat)
  ensures f == fib(n)
  decreases n
{
  if n == 0 {
    f := 0;
  } else {
    var i := 1;
    var fant := 0;
    f := 1;
    while i < n
      invariant fant == fib(i - 1) && f == fib(i)
      invariant i <= n
      decreases n - i
    {
      fant, f := f, fant + f;
      i := fant + 1;
    }
  }
}

method fibonacci3(n: nat) returns (f: nat)
  ensures f == fib(n)
  decreases n
{
  {
    var i: int := 0;
    var a := 1;
    f := 0;
    while i < n
      invariant 0 <= i <= n
      invariant if i == 0 then a == fib(i + 1) && f == fib(i) else a == fib(i - 1) && f == fib(i)
      decreases n - i
    {
      a, f := f, a + f;
      i := i + 1;
    }
  }
}
