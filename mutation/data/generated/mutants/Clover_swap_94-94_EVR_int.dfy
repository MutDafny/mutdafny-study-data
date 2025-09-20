// Clover_swap.dfy

method Swap(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
  decreases X, Y
{
  x, y := 0, Y;
  var tmp := x;
  x := y;
  y := tmp;
  assert x == Y && y == X;
}
