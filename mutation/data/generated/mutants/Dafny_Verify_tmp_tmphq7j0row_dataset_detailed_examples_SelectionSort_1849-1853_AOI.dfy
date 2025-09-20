// Dafny_Verify_tmp_tmphq7j0row_dataset_detailed_examples_SelectionSort.dfy

method SelectionSort(a: array<int>)
  modifies a
  ensures forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
  decreases a
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length && j < n ==> a[i] <= a[j]
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> forall j: int {:trigger a[j]} :: n <= j < a.Length ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= mindex < a.Length
      invariant n <= m <= a.Length
      invariant forall i: int {:trigger a[i]} :: n <= i < m ==> a[mindex] <= a[i]
      invariant multiset(a[..]) == old(multiset(a[..]))
      decreases if m <= a.Length then a.Length - m else m - a.Length
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
    }
    n := -(n + 1);
  }
}
