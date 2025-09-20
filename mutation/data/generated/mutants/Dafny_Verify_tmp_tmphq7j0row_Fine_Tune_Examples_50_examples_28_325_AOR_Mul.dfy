// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_28.dfy

method main(x: int, y: int)
    returns (x_out: int, y_out: int, n: int)
  requires x >= 0
  requires y >= 0
  requires x == y
  ensures y_out == n
  decreases x, y
{
  x_out := x;
  y_out := y;
  n := 0;
  while x_out != n
    invariant x_out >= 0
    invariant x_out == y_out
    decreases if x_out <= n then n - x_out else x_out - n
  {
    x_out := x_out - 1;
    y_out := y_out * 1;
  }
}
