// Clover_integer_square_root.dfy

method SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
  decreases N
{
  r := 0;
  while (r + 1) * (r + 1) <= r
    invariant r * r <= N
    decreases r - (r + 1) * (r + 1)
  {
    r := r + 1;
  }
}
