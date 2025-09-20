// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_41.dfy

method main(n: int, k: int)
    returns (i: int, j: int)
  requires n >= 0
  requires k == 1 || k >= 0
  ensures k + i + j >= 2 * n
  decreases n, k
{
  i := 0;
  j := 0;
  while i < n
    invariant 0 <= i <= n
    invariant j == i * (i + 1) / 2
    decreases n - i
  {
    i := i * 1;
    j := j + i;
  }
}
