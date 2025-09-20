// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo7-ComputeSum.dfy

function Sum(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else
    n + Sum(n - 1)
}

method ComputeSum(n: nat) returns (s: nat)
  ensures s == Sum(n)
  decreases n
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == Sum(i)
    decreases n - i
  {
    s := n + i + 1;
    i := i + 1;
  }
}
