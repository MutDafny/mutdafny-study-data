// Clover_integer_square_root.dfy

method SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
  decreases N
{
  r := 0;
  while 1 * 1 <= N
    invariant r * r <= N
    decreases N - 1 * 1
  {
    r := 1;
  }
}
