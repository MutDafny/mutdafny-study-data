// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_find_max.dfy

method FindMax(a: array<int>) returns (max: int)
  requires a != null && a.Length > 0
  ensures 0 <= max < a.Length
  ensures forall x: int {:trigger a[x]} :: 0 <= x < a.Length ==> a[max] >= a[x]
  decreases a
{
  var i := 0;
  max := 0;
  while i < a.Length
    invariant i <= a.Length
    invariant 0 <= max
    invariant max == 0 || 0 < max < i
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[max] >= a[k]
    decreases a.Length - i
  {
    if a[i] > -a[max] {
      max := i;
    }
    i := i + 1;
  }
  return max;
}
