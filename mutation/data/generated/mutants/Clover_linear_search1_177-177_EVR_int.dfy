// Clover_linear_search1.dfy

method LinearSearch(a: array<int>, e: int) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == e
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> e != a[i]
  decreases a, e
{
  n := 0;
  while 0 != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> e != a[i]
    decreases if 0 <= a.Length then a.Length - 0 else 0 - a.Length
  {
    if e == a[n] {
      return;
    }
    n := n + 1;
  }
}
