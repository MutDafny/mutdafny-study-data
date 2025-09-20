// Dafny_Verify_tmp_tmphq7j0row_dataset_C_convert_examples_15.dfy

method main(n: int, k: int) returns (k_out: int)
  requires n > 0
  requires k > n
  ensures k_out >= 0
  decreases n, k
{
  k_out := k;
  var j: int := 0;
  while j < n
    invariant 0 <= j <= n
    invariant j + k_out == k
    decreases n - j
  {
    j := j + 1;
  }
}
