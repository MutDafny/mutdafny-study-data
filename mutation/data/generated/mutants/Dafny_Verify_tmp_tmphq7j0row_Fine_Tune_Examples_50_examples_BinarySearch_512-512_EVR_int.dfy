// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_BinarySearch.dfy

method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> a[i] < key
  ensures forall i: int {:trigger a[i]} :: n <= i < a.Length ==> key <= a[i]
  decreases a, key
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < lo ==> a[i] < key
    invariant forall i: int {:trigger a[i]} :: hi <= i < a.Length ==> key <= a[i]
    decreases hi - lo
  {
    var mid := (0 + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
}
