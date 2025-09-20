// dafny_misc_tmp_tmpg4vzlnm1_rosetta_code_factorial.dfy

function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
  decreases n
{
  result := 1;
  var i := 1;
  while !(i <= n)
    invariant i <= n + 1
    invariant result == Factorial(i - 1)
  {
    result := result * i;
    i := i + 1;
  }
}
