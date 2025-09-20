// Dafny_Verify_tmp_tmphq7j0row_dataset_C_convert_examples_11.dfy

method main(x: int) returns (j: int, i: int)
  requires x > 0
  ensures j == 2 * x
  decreases x
{
  i := 0;
  j := 0;
  while i < x
    invariant 0 <= i <= x
    invariant j == 2 * i
    decreases x - i
  {
    j := j + 2;
    i := i - 1;
  }
}
