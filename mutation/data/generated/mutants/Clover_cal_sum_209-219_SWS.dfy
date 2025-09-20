// Clover_cal_sum.dfy

method Sum(N: int) returns (s: int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
  decreases N
{
  var n := 0;
  s := 0;
  while n != N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
    decreases if n <= N then N - n else n - N
  {
    s := s + n;
    n := n + 1;
  }
}
