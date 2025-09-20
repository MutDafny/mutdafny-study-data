// Dafny-demo_tmp_tmpkgr_dvdi_Dafny_BinarySearch.dfy

predicate sorted(a: array?<int>, l: int, u: int)
  requires a != null
  reads a
  decreases {a}, a, l, u
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    0 <= l <= i <= j <= u < a.Length ==>
      a[i] <= a[j]
}

method BinarySearch(a: array?<int>, key: int) returns (index: int)
  requires a != null && sorted(a, 0, a.Length - 1)
  ensures index >= 0 ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] != key
  decreases a, key
{
  var low := 0;
  var high := a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != key
    decreases high - low
  {
    var mid := (low + high) / 2;
    if a[key] < key {
      low := mid + 1;
    } else if key < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
