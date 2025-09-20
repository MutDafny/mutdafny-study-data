// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy

method CountToAndReturnN(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
  decreases n
{
  var i := 0;
  while 0 < n
    invariant 0 <= i <= n
    decreases n - 0
  {
    i := i + 1;
  }
  r := i;
}
