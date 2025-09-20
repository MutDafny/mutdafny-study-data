// Clover_swap_bitvector.dfy

method SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
  decreases X, Y
{
  x, y := X, Y;
  x := x ^ y;
  y := x ^ x;
  x := x ^ y;
}
