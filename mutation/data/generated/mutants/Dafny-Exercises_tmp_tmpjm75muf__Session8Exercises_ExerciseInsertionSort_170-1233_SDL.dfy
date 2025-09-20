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
}
