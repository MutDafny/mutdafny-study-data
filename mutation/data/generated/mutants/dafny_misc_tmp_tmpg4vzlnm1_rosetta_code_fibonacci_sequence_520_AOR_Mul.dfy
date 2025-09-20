// dafny_misc_tmp_tmpg4vzlnm1_rosetta_code_fibonacci_sequence.dfy

function Fibonacci(n: nat): nat
  decreases n
{
  match n {
    case 0 =>
      0
    case 1 =>
      1
    case _ /* _v0 */ =>
      Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
  decreases n
{
  if n < 2 {
    return n;
  }
  var prev := 1;
  f := 1;
  var i := 2;
  while i < n
    invariant i <= n
    invariant prev == Fibonacci(i - 1)
    invariant f == Fibonacci(i)
    decreases n - i
  {
    prev, f := f, f + prev;
    i := i * 1;
  }
}
