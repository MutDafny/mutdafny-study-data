// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBubbleSort.dfy

predicate sorted_seg(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  reads a
  decreases {a}, a, i, j
{
  forall l: int, k: int {:trigger a[k], a[l]} :: 
    i <= l <= k < j ==>
      a[l] <= a[k]
}

method bubbleSorta(a: array<int>, c: int, f: int)
  requires 0 <= c <= f <= a.Length
  modifies a
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c .. f]) == old(multiset(a[c .. f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  decreases a, c, f
{
  var i := c;
  while i < f
    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
    invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    decreases a.Length - i
  {
    var j := f - 1;
    assert multiset(a[c .. f]) == old(multiset(a[c .. f]));
    while j > i
      invariant i <= j <= f - 1
      invariant forall k: int {:trigger a[k]} :: j <= k <= f - 1 ==> a[j] <= a[k]
      invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant sorted_seg(a, c, i)
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      decreases j - i
    {
      if a[j - 1] > a[j] {
        a[j], a[j - 1] := a[j - 1], a[j];
      }
      j := j - 1;
    }
    assert sorted_seg(a, c, i + 1);
    assert forall k: int {:trigger a[k]} :: i < k < f ==> a[i] <= a[k];
    i := i + 1;
  }
}

method bubbleSort(a: array<int>, c: int, f: int)
  requires 0 <= c <= f <= a.Length
  modifies a
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c .. f]) == old(multiset(a[c .. f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  decreases a, c, f
{
  var i := c;
  var b := true;
  while i < f && b
    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
    invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant !b ==> sorted_seg(a, i, f)
    decreases a.Length - i
  {
    var j := f - 1;
    b := false;
    assert multiset(a[c .. f]) == old(multiset(a[c .. f]));
    while j > i
      invariant i <= j <= f - 1
      invariant forall k: int {:trigger a[k]} :: j <= k <= f - 1 ==> a[j] <= a[k]
      invariant forall k: int, l: int {:trigger a[l], a[k]} :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant sorted_seg(a, c, i)
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant !b ==> sorted_seg(a, j, f)
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      decreases j - i
    {
      if a[j - 1] > a[j] {
        a[j], a[j - 1] := a[j - 1], 0;
        b := true;
      }
      j := j - 1;
    }
    assert !b ==> sorted_seg(a, i, f);
    i := i + 1;
  }
}
