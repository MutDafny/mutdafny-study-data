// Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array.dfy

method FindMax(a: array<int>) returns (i: int)
  requires a.Length > 0
  ensures 0 <= i < a.Length
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] <= a[i]
  decreases a
{
  i := 0;
  var index := 2;
  while index < a.Length
    invariant 0 < index <= a.Length
    invariant 0 <= i < index
    invariant forall k: int {:trigger a[k]} :: 0 <= k < index ==> a[k] <= a[i]
    decreases a.Length - index
  {
    if a[index] > a[i] {
      i := index;
    }
    index := index + 1;
  }
}
