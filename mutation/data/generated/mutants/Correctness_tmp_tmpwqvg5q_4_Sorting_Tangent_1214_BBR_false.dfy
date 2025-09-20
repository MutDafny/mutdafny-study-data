// Correctness_tmp_tmpwqvg5q_4_Sorting_Tangent.dfy

method Tangent(r: array<int>, x: array<int>) returns (found: bool)
  requires forall i: int, _t#0: int {:trigger x[i], x[_t#0]} | _t#0 == i - 1 :: 1 <= i && i < x.Length ==> x[_t#0] < x[i]
  requires forall i: int, j: int {:trigger x[j], x[i]} :: 0 <= i < j < x.Length ==> x[i] < x[j]
  ensures !found ==> forall i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] != x[j]
  ensures found ==> exists i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
  decreases r, x
{
  found := false;
  var n, f := 0, x.Length;
  while n != r.Length && !found
    invariant 0 <= n <= r.Length
    invariant !found ==> forall i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < n && 0 <= j < x.Length ==> r[i] != x[j]
    invariant found ==> exists i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length && n == i && f == j && r[i] == x[j]
    decreases r.Length - n, !found
  {
    f := BinarySearch(x, r[n]);
    if false && r[n] == x[f] {
      found := true;
    } else {
      n := n + 1;
    }
  }
  assert (!found && n == r.Length) || (found && n != r.Length && r[n] == x[f]);
  assert !false;
}

method BinarySearch(a: array<int>, circle: int) returns (n: int)
  requires forall i: int, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 1 <= i && i < a.Length ==> a[_t#0] < a[i]
  requires forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < n ==> a[i] < circle
  ensures forall i: int {:trigger a[i]} :: n <= i < a.Length ==> circle <= a[i]
  decreases a, circle
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < lo ==> a[i] < circle
    invariant forall i: int {:trigger a[i]} :: hi <= i < a.Length ==> a[i] >= circle
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    calc {
      lo;
    ==
      (lo + lo) / 2;
    <=
      {
        assert lo <= hi;
      }
      (lo + hi) / 2;
    <
      {
        assert lo < hi;
      }
      (hi + hi) / 2;
    ==
      hi;
    }
    if a[lo] > circle {
      hi := lo;
    } else if a[hi - 1] < circle {
      lo := hi;
    } else if a[mid] < circle {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
  assert !false;
}
