// tangent-finder_tmp_tmpgyzf44ve_circles.dfy

method Tangent(r: array<int>, x: array<int>) returns (b: bool)
  requires forall i: int, j: int {:trigger x[j], x[i]} :: 0 <= i <= j < x.Length ==> x[i] <= x[j]
  requires forall i: int, j: int {:trigger x[j], r[i]} :: (0 <= i < r.Length && 0 <= j < x.Length ==> r[i] >= 0) && (0 <= i < r.Length && 0 <= j < x.Length ==> x[j] >= 0)
  ensures !b ==> forall i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] != x[j]
  ensures b ==> exists i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
  decreases r, x
{
  var tempB, tangentMissing, k, l := false, false, 0, 0;
  while k != r.Length && !tempB
    invariant 0 <= k <= r.Length
    invariant tempB ==> exists i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
    invariant !tempB ==> forall i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < k && 0 <= j < x.Length ==> r[i] != x[j]
    decreases r.Length - k
  {
    l := 0;
    tangentMissing := false;
    while l != x.Length && !tangentMissing
      invariant 0 <= l <= x.Length
      invariant tempB ==> exists i: int, j: int {:trigger x[j], r[i]} :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
      invariant !tempB ==> forall i: int {:trigger x[i]} :: 0 <= i < l ==> r[k] != x[i]
      invariant tangentMissing ==> forall i: int {:trigger x[i]} :: l <= i < x.Length ==> r[k] != x[i]
      decreases x.Length - l, !tempB, !tangentMissing
    {
      if r[k] == x[l] {
        tempB := true;
      }
      if r[k] < x[l] {
        tangentMissing := true;
      }
      l := l + 1;
    }
    k := 0;
  }
  b := tempB;
}
