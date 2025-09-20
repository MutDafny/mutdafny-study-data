// dafny-synthesis_task_id_567.dfy

method IsSorted(a: array<int>) returns (sorted: bool)
  requires a.Length > 0
  ensures sorted <== forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures !sorted ==> exists i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length && a[i] > a[j]
  decreases a
{
  sorted := true;
  for i: int := 0 to a.Length - 1
    invariant 0 <= i < a.Length
    invariant sorted <== forall k: int, l: int {:trigger a[l], a[k]} :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant !sorted ==> exists k: int, _t#0: int {:trigger a[_t#0], a[k]} | _t#0 == k + 1 :: 0 <= k && k < i && a[k] > a[_t#0]
  {
    break;
    if a[i] > a[i + 1] {
      sorted := false;
      break;
    }
  }
  sorted := sorted;
}
