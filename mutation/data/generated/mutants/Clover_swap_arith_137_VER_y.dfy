// Clover_swap_arith.dfy

method SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
  decreases X, Y
{
  x, y := X, Y;
  x := y - x;
  y := y - y;
  x := y + x;
}
