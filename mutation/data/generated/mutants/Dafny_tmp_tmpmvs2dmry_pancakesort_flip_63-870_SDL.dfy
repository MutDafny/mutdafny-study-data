// Dafny_tmp_tmpmvs2dmry_pancakesort_flip.dfy

method flip(a: array<int>, num: int)
  requires a.Length > 0
  requires 0 <= num < a.Length
  modifies a
  ensures forall k: int {:trigger a[k]} :: 0 <= k <= num ==> a[k] == old(a[num - k])
  ensures forall k: int {:trigger old(a[k])} {:trigger a[k]} :: num < k < a.Length ==> a[k] == old(a[k])
  decreases a, num
{
}
