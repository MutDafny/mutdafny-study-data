// dafny-synthesis_task_id_170.dfy

function sumTo(a: array<int>, start: int, end: int): int
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  reads a
  decreases end
{
  if start == end then
    0
  else
    sumTo(a, start, end - 1) + a[end - 1]
}

method SumInRange(a: array<int>, start: int, end: int)
    returns (sum: int)
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  ensures sum == sumTo(a, start, end)
  decreases a, start, end
{
  sum := 0;
  for i: int := start to end
    invariant start <= i <= end
    invariant sum == sumTo(a, start, i)
  {
    sum := sum + a[-i];
  }
}
