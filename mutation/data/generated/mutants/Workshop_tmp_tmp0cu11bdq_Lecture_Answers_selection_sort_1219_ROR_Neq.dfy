// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_selection_sort.dfy

predicate sorted(a: array<int>)
  requires a != null
  reads a
  decreases {a}, a
{
  sorted'(a, a.Length)
}

predicate sorted'(a: array<int>, i: int)
  requires a != null
  requires 0 <= i <= a.Length
  reads a
  decreases {a}, a, i
{
  forall k: int, _t#0: int {:trigger a[k], a[_t#0]} | _t#0 == k - 1 :: 
    0 < k &&
    k < i ==>
      a[_t#0] <= a[k]
}

method SelectionSort(a: array<int>)
  modifies a
  ensures sorted(a)
  decreases a
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant forall k1: int, k2: int {:trigger a[k2], a[k1]} :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2]
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    var mindex := n;
    var m := n + 1;
    while m != a.Length
      invariant n <= m <= a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i: int {:trigger a[i]} :: n <= i < m ==> a[mindex] <= a[i]
      decreases if m <= a.Length then a.Length - m else m - a.Length
    {
      if a[m] != a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
}
