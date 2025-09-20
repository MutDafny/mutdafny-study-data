// Dafny_Verify_tmp_tmphq7j0row_dataset_C_convert_examples_23_x.dfy

method main(n: int) returns (sum: int, i: int)
  requires n >= 0
  decreases n
{
  sum := 0;
  i := -1;
  while i < n
    invariant sum >= 0
    invariant 0 <= i <= n
    decreases n - i
  {
    sum := sum + i;
    i := i + 1;
  }
}
