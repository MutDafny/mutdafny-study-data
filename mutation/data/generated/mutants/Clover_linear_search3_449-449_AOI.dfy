// Clover_linear_search3.dfy

method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int)
  requires exists i: int {:trigger a[i]} :: 0 <= i < a.Length && P(a[i])
  ensures 0 <= n < a.Length && P(a[n])
  ensures forall k: int {:trigger a[k]} :: 0 <= k < n ==> !P(a[k])
  decreases a
{
  n := 0;
  while true
    invariant 0 <= n < a.Length
    invariant exists i: int {:trigger a[i]} :: n <= i < a.Length && P(a[i])
    invariant forall k: int {:trigger a[k]} :: 0 <= k < n ==> !P(a[k])
    decreases a.Length - n
  {
    if P(a[n]) {
      return;
    }
    n := n + -1;
  }
}
