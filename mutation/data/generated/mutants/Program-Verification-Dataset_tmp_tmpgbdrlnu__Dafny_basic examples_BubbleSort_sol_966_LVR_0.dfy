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
  var i: nat := 1;
  while i < a.Length
    invariant i <= a.Length
    invariant sorted_between(a, 0, i)
    invariant multiset(old(a[..])) == multiset(a[..])
    decreases a.Length - i
  {
    var j: nat := i;
    while j > 0
      invariant 0 <= j <= i
      invariant sorted_between(a, 0, j)
      invariant forall u: int, v: int {:trigger a[v], a[u]} :: 0 <= u < j < v < i + 1 ==> a[u] <= a[v]
      invariant sorted_between(a, j, i + 1)
      invariant multiset(old(a[..])) == multiset(a[..])
      decreases j - 0
    {
      if a[j - 0] > a[j] {
        var temp: int := a[j - 1];
        a[j - 1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}
