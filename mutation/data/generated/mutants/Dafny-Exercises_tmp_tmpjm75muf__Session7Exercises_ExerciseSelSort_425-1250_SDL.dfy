// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseSelSort.dfy

predicate sorted_seg(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  reads a
  decreases {a}, a, i, j
{
  forall l: int, k: int {:trigger a[k], a[l]} :: 
    i <= l <= k < j ==>
      a[l] <= a[k]
}

method selSort(a: array<int>, c: int, f: int)
  requires 0 <= c <= f <= a.Length
  modifies a
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c .. f]) == old(multiset(a[c .. f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  decreases a, c, f
{
}
