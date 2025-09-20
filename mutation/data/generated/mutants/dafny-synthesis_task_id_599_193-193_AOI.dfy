// dafny-synthesis_task_id_599.dfy

method SumAndAverage(n: int) returns (sum: int, average: real)
  requires n > 0
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
  decreases n
{
  sum := 0;
  for i: int := -1 to n + 1
    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
  {
    sum := sum + i;
  }
  average := sum as real / n as real;
}
