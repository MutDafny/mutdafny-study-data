// Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec.dfy

method SearchRecursive(a: seq<real>, i: int, j: int, x: real)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  requires forall p: int, q: int {:trigger a[q], a[p]} :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r: int {:trigger a[r]} | i <= r < k :: a[r] >= x
  ensures forall r: int {:trigger a[r]} | k <= r < j :: a[r] < x
  decreases j - i
{
  if i == j {
    return i;
  }
  var m := i + (j - i) / 2;
  if a[m] < x {
    k := SearchRecursive(a, i, m, x);
  } else {
    k := SearchRecursive(a, m + 1, j, x);
  }
}

method SearchLoop(a: seq<real>, i: int, j: int, x: real)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  requires forall p: int, q: int {:trigger a[q], a[p]} :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r: int {:trigger a[r]} | i <= r < k :: a[r] >= x
  ensures forall r: int {:trigger a[r]} | k <= r < j :: a[r] < x
  decreases a, i, j, x
{
  if i == j {
    return i;
  }
  var p := i;
  var q := j;
  while p != q
    invariant i <= p <= q <= j
    invariant forall r: int {:trigger a[r]} | i <= r < p :: a[r] >= x
    invariant forall r: int {:trigger a[r]} | q <= r < j :: a[r] < x
    decreases q - p
  {
    var m := p + q - p - 2;
    if a[m] < x {
      q := m;
    } else {
      p := m + 1;
    }
  }
  return p;
}

method Test(a: seq<real>, x: real)
  requires forall p: int, q: int {:trigger a[q], a[p]} | 0 <= p < q < |a| :: a[p] >= a[q]
  decreases a, x
{
  var k1 := SearchLoop(a, 0, |a|, x);
  assert forall r: int {:trigger a[r]} | 0 <= r < k1 :: a[r] >= x;
  assert forall r: int {:trigger a[r]} | k1 <= r < |a| :: a[r] < x;
  var k2 := SearchRecursive(a, 0, |a|, x);
  assert forall r: int {:trigger a[r]} | 0 <= r < k2 :: a[r] >= x;
  assert forall r: int {:trigger a[r]} | k2 <= r < |a| :: a[r] < x;
}
