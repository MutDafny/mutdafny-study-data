// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Minimum.dfy

method Minimum(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures exists i: int {:trigger a[i]} :: 0 <= i < a.Length && m == a[i]
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> m <= a[i]
  decreases a
{
  var n := 0;
  m := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant exists i: int {:trigger a[i]} :: 0 <= i < a.Length && m == a[i]
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> m <= a[i]
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    if a[n] < m {
      m := a[n];
    }
    n := n + 1;
  }
}
