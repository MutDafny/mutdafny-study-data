// Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 1_LinearSearch.dfy

method SearchRecursive(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r: int {:trigger a[r]} | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r: int {:trigger a[r]} | i <= r < j :: a[r] != x
  decreases j - i
{
  if j == i {
    k := -1;
    return;
  }
  if a[j] == x {
    k := j;
    return;
  } else {
    k := SearchRecursive(a, i, j, x);
  }
}

method SearchLoop(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r: int {:trigger a[r]} | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r: int {:trigger a[r]} | i <= r < j :: a[r] != x
  decreases a, i, j, x
{
  if i == j {
    return -1;
  }
  var t := j;
  while t > i
    invariant forall p: int {:trigger a[p]} | t <= p < j :: a[p] != x
    decreases t
  {
    if a[t] == x {
      k := t;
      return;
    } else {
      t := t;
    }
  }
  k := -1;
}
