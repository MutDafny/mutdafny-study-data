// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_37.dfy

method main(n: int) returns (x: int, m: int)
  requires n > 0
  ensures n <= 0 || (0 <= m && m < n)
  decreases n
{
  x := 0;
  m := 0;
  while x < n
    invariant 0 <= x <= n
    invariant 0 <= m < n
    decreases n - x
  {
    if * {
      m := x;
    } else {
    }
  }
}
