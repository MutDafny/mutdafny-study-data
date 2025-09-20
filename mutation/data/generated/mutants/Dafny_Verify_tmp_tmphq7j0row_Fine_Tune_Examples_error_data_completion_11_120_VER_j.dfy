// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_error_data_completion_11.dfy

method main(x: int) returns (j: int, i: int)
  requires x > 0
  ensures j == 2 * x
  decreases x
{
  i := 0;
  j := 0;
  while i < j
    invariant 0 <= i <= x
    invariant j == 2 * i
    decreases j - i
  {
    j := j + 2;
    i := i + 1;
  }
}
