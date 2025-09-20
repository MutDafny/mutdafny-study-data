// Clover_binary_search.dfy

method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i: int {:trigger a[i]} :: n <= i < a.Length ==> a[i] >= key
  decreases a, key
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < lo ==> a[i] < key
    invariant forall i: int {:trigger a[i]} :: hi <= i < a.Length ==> a[i] >= key
    decreases hi - lo
  {
    var mid := (lo + hi) / 3;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
}
