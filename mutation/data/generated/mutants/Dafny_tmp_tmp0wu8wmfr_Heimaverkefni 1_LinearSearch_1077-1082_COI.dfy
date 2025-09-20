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
  if !(j == i) {
    k := -1;
    return;
  }
  if a[j - 1] == x {
    k := j - 1;
    return;
  } else {
    k := SearchRecursive(a, i, j - 1, x);
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
    if a[t - 1] == x {
      k := t - 1;
      return;
    } else {
      t := t - 1;
    }
  }
  k := -1;
}
