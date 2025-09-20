// Dafny_Verify_tmp_tmphq7j0row_dataset_C_convert_examples_07.dfy

method main(n: int) returns (a: int, b: int)
  requires n >= 0
  ensures a + b == 3 * n
  decreases n
{
  var i: int := 0;
  a := 0;
  b := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a + b == 3 * i
    decreases n - i
  {
    if * {
      a := a + 1;
      b := b + 2;
    } else {
      a := a + 2;
      b := a + 1;
    }
    i := i + 1;
  }
}
