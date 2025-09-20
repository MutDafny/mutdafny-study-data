// Dafny_tmp_tmpmvs2dmry_pancakesort_flip.dfy

method flip(a: array<int>, num: int)
  requires a.Length > 0
  requires 0 <= num < a.Length
  modifies a
  ensures forall k: int {:trigger a[k]} :: 0 <= k <= num ==> a[k] == old(a[num - k])
  ensures forall k: int {:trigger old(a[k])} {:trigger a[k]} :: num < k < a.Length ==> a[k] == old(a[k])
  decreases a, num
{
  var tmp: int;
  var i := 0;
  var j := num;
  while i < j
    invariant i + j == num
    invariant 0 <= i <= num / 2 + 1
    invariant num / 2 <= j <= num
    invariant forall n: int {:trigger a[n]} :: 0 <= n < i ==> a[n] == old(a[num - n])
    invariant forall n: int {:trigger old(a[n])} :: 0 <= n < i ==> a[num - n] == old(a[n])
    invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: i <= k <= j ==> a[k] == old(a[k])
    invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: num < k < a.Length ==> a[k] == old(a[k])
    decreases j
  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := -j - 1;
  }
}
