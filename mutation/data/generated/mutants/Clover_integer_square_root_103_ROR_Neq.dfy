// Clover_integer_square_root.dfy

method SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
  decreases N
{
  r := 0;
  while (r + 1) * (r + 1) != N
    invariant r * r <= N
    decreases if (r + 1) * (r + 1) <= N then N - (r + 1) * (r + 1) else (r + 1) * (r + 1) - N
  {
    r := r + 1;
  }
}
