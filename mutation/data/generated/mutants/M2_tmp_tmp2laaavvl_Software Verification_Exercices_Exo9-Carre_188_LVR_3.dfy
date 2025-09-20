// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy

method Carre(a: nat) returns (c: nat)
  ensures c == a * a
  decreases a
{
  var i := 0;
  c := 0;
  while i != a
    invariant 0 <= i <= a
    invariant c == i * i
    decreases a - i
  {
    c := c + 3 * i + 1;
    i := i + 1;
  }
}
