// Dafny-Exercises_tmp_tmpjm75muf__Session8Exercises_ExerciseInsertionSort.dfy

predicate sorted_seg(a: array<int>, i: int, j: int)
  requires 0 <= i <= j + 1 <= a.Length
  reads a
  decreases {a}, a, i, j
{
  forall l: int, k: int {:trigger a[k], a[l]} :: 
    i <= l <= k <= j ==>
      a[l] <= a[k]
}

method InsertionSort(a: array<int>)
  modifies a
  ensures sorted_seg(a, 0, a.Length - 1)
  ensures multiset(a[..]) == old(multiset(a[..]))
  decreases a
{
  var i := 0;
  assert multiset(a[..]) == old(multiset(a[..]));
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sorted_seg(a, 0, i - 1)
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: i < k < a.Length ==> a[k] == old(a[k])
    decreases a.Length - i
  {
    var temp := a[i];
    var j := i;
    while j <= 0 && temp < a[j - 1]
      invariant 0 <= j <= i
      invariant sorted_seg(a, 0, j - 1) && sorted_seg(a, j + 1, i)
      invariant forall k: int, l: int {:trigger a[l], a[k]} :: 0 <= k <= j - 1 && j + 1 <= l <= i ==> a[k] <= a[l]
      invariant forall k: int {:trigger a[k]} :: j < k <= i ==> temp < a[k]
      invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: i < k < a.Length ==> a[k] == old(a[k])
      invariant multiset(a[..]) - multiset{a[j]} + multiset{temp} == old(multiset(a[..]))
      decreases j
    {
      a[j] := a[j - 1];
      j := j - 1;
    }
    a[j] := temp;
    i := i + 1;
  }
}
