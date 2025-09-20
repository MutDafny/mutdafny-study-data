// dafny-synthesis_task_id_145.dfy

method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 1
  ensures forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
  decreases a
{
  var minVal := a[0];
  var maxVal := a[0];
  for i: int := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k: int {:trigger a[k]} :: (0 <= k < i ==> minVal <= a[k]) && (0 <= k < i ==> a[k] <= maxVal)
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[minVal];
    }
  }
  diff := maxVal - minVal;
}
