// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_LinearSearch.dfy

method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> !P(a[i])
  decreases a
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> !P(a[i])
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    if P(a[n]) {
      return;
    }
    n := n - 1;
  }
}
