// dafny-synthesis_task_id_622.dfy

method FindMedian(a: array<int>, b: array<int>) returns (median: int)
  requires a != null && b != null
  requires a.Length == b.Length
  requires a.Length > 0
  requires forall i: int, _t#0: int {:trigger a[_t#0], a[i]} | _t#0 == i + 1 :: 0 <= i && i < a.Length - 1 ==> a[i] <= a[_t#0]
  requires forall i: int, _t#0: int {:trigger b[_t#0], b[i]} | _t#0 == i + 1 :: 0 <= i && i < b.Length - 1 ==> b[i] <= b[_t#0]
  ensures median == if a.Length % 2 == 0 then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
  decreases a, b
{
  if -a.Length % 2 == 0 {
    median := (a[a.Length / 2 - 1] + b[0]) / 2;
  } else {
    median := a[a.Length / 2];
  }
}
