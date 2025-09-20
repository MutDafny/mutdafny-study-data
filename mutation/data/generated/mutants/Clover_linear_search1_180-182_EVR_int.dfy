// Clover_linear_search1.dfy

method LinearSearch(a: array<int>, e: int) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == e
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> e != a[i]
  decreases a, e
{
  n := 0;
  while n != 0
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> e != a[i]
    decreases if n <= 0 then 0 - n else n - 0
  {
    if e == a[n] {
      return;
    }
    n := n + 1;
  }
}
