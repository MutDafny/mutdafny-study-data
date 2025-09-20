// dafny-synthesis_task_id_751.dfy

method IsMinHeap(a: array<int>) returns (result: bool)
  requires a != null
  ensures result ==> (forall i: int, _t#0: int {:trigger a[_t#0], a[i]} {:trigger a[_t#0], 2 * i} | _t#0 == 2 * i + 1 :: 0 <= i && i < a.Length / 2 ==> a[i] <= a[_t#0]) && forall i: int, _t#0: int {:trigger a[_t#0], a[i]} {:trigger a[_t#0], 2 * i} | _t#0 == 2 * i + 2 :: 0 <= i && i < a.Length / 2 ==> _t#0 == a.Length || a[i] <= a[_t#0]
  ensures !result ==> (exists i: int, _t#0: int {:trigger a[_t#0], a[i]} {:trigger a[_t#0], 2 * i} | _t#0 == 2 * i + 1 :: 0 <= i && i < a.Length / 2 && a[i] > a[_t#0]) || exists i: int, _t#0: int {:trigger a[_t#0], a[i]} {:trigger a[_t#0], 2 * i} | _t#0 == 2 * i + 2 :: 0 <= i && i < a.Length / 2 && _t#0 != a.Length && a[i] > a[_t#0]
  decreases a
{
  result := true;
  for i: int := 0 to a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant result ==> (forall k: int, _t#0: int {:trigger a[_t#0], a[k]} {:trigger a[_t#0], 2 * k} | _t#0 == 2 * k + 1 :: 0 <= k && k < i ==> a[k] <= a[_t#0]) && forall k: int, _t#0: int {:trigger a[_t#0], a[k]} {:trigger a[_t#0], 2 * k} | _t#0 == 2 * k + 2 :: 0 <= k && k < i ==> _t#0 == a.Length || a[k] <= a[_t#0]
  {
    if a[i] > a[2 * i + 1] || (2 * i + 2 != a.Length && a[i] > a[2 * i + 2]) {
      break;
    }
  }
}
