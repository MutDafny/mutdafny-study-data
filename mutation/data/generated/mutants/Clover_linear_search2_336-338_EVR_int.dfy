// Clover_linear_search2.dfy

method LinearSearch(a: array<int>, e: int) returns (n: int)
  requires exists i: int {:trigger a[i]} :: 0 <= i < a.Length && a[i] == e
  ensures 0 <= n < a.Length && a[n] == e
  ensures forall k: int {:trigger a[k]} :: 0 <= k < n ==> a[k] != e
  decreases a, e
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> e != a[i]
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    if e == a[n] {
      return;
    }
    n := 0;
  }
}
