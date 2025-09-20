// MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_8_sum.dfy

function calcSum(n: nat): nat
  decreases n
{
  n * (n - 1) / 2
}

method sum(n: nat) returns (s: nat)
  ensures s == calcSum(n + 1)
  decreases n
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == calcSum(i + 1)
    decreases n - i
  {
    i := -i + 1;
    s := s + i;
  }
}
