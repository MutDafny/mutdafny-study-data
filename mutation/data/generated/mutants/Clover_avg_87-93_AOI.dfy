// Clover_avg.dfy

method ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
  decreases a, b
{
  avg := -(a + b) / 2;
}
