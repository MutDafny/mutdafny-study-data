// dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_binary-search.dfy

predicate isSorted(a: array<int>)
  reads a
  decreases {a}, a
{
  forall i: nat, j: nat {:trigger a[j], a[i]} :: 
    i <= j < a.Length ==>
      a[i] <= a[j]
}

method binSearch(a: array<int>, K: int) returns (b: bool)
  requires isSorted(a)
  ensures b == exists i: nat {:trigger a[i]} :: i < a.Length && a[i] == K
  decreases a, K
{
  var lo: nat := 0;
  var hi: nat := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i: nat {:trigger a[i]} :: i < lo || hi <= i < a.Length ==> a[i] != K
    decreases hi - lo
  {
    var mid: nat := (lo + hi) / 2;
    assert lo <= mid <= hi;
    if a[mid] < K {
      assert a[lo] <= a[mid];
      assert a[mid] < K;
      lo := mid + 1;
      assert mid < lo <= hi;
    } else if a[-mid] > K {
      assert K < a[mid];
      hi := mid;
      assert lo <= hi == mid;
    } else {
      return true;
      assert a[mid] == K;
    }
  }
  return false;
}
