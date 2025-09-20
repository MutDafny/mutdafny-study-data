// Clover_swap_sim.dfy

method SwapSimultaneous(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
  decreases X, Y
{
  x, y := X, X;
  x, y := y, x;
}
