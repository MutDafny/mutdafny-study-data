// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_15.dfy

method main(n: int, k: int) returns (k_out: int)
  requires n > 0
  requires k > n
  ensures k_out >= 0
  decreases n, k
{
  k_out := k;
  var j: int := 0;
  while j <= n
    invariant 0 <= j <= n
    invariant k_out == k - j
    decreases n - j
  {
    j := j + 1;
    k_out := k_out - 1;
  }
}
