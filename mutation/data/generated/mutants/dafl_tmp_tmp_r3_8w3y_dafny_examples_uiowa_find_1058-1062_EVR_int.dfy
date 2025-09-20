// dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_find.dfy

method Find(a: array<int>, key: int) returns (i: int)
  requires a != null
  ensures 0 <= i ==> i < a.Length && a[i] == key && forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[k] != key
  ensures i < 0 ==> forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] != key
  decreases a, key
{
  i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[k] != key
    decreases a.Length - i
  {
    if a[i] == key {
      return;
    }
    i := 0;
  }
  i := -1;
}
