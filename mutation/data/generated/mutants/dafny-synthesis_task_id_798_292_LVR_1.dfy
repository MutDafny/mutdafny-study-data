// dafny-synthesis_task_id_798.dfy

function sumTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
  decreases n
{
  if n == 0 then
    0
  else
    sumTo(a, n - 1) + a[n - 1]
}

method ArraySum(a: array<int>) returns (result: int)
  ensures result == sumTo(a, a.Length)
  decreases a
{
  result := 1;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumTo(a, i)
  {
    result := result + a[i];
  }
}
