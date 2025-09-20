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
  if c <= f - 1 {
    var i := c;
    while i < f - 1
      invariant c <= i <= f
      invariant sorted_seg(a, c, i)
      invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      decreases f - i
    {
      var less := i;
      var j := i + 1;
      while j < f
        invariant i + 1 <= j <= f
        invariant i <= less < f
        invariant sorted_seg(a, c, i)
        invariant forall k: int {:trigger a[k]} :: i <= k < j ==> a[less] <= a[k]
        invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
        invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        decreases f - j
      {
        if a[j] < a[i] {
          less := j;
        }
        j := j + 1;
      }
      a[i], a[less] := a[less], a[i];
      i := i + 1;
    }
  }
}
