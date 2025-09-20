// se2011_tmp_tmp71eb82zt_ass1_ex6.dfy

method Ceiling7(n: nat) returns (k: nat)
  requires n >= 0
  ensures k == n - n % 7
  decreases n
{
  k := n - n % 7;
}

method test7()
{
}
