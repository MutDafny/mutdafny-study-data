// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_BubbleSort_sol.dfy

predicate sorted_between(a: array<int>, from: nat, to: nat)
  requires a != null
  requires from <= to
  requires to <= a.Length
  reads a
  decreases {a}, a, from, to
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    from <= i < j < to &&
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}

predicate sorted(a: array<int>)
  requires a != null
  reads a
  decreases {a}, a
{
  sorted_between(a, 0, a.Length)
}

method bubbleSort(a: array<int>)
  requires a != null
  requires a.Length > 0
  modifies a
  ensures sorted(a)
  ensures multiset(old(a[..])) == multiset(a[..])
  decreases a
{
}
