// Software-Verification_tmp_tmpv4ueky2d_Non-overlapping Intervals_non_overlapping_intervals.dfy

method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
  requires 1 <= intervals.Length0 <= 100000
  requires intervals.Length1 == 2
  requires forall i: int {:trigger intervals[i, 0]} :: (0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0]) && (0 <= i < intervals.Length0 ==> intervals[i, 0] <= 50000)
  requires forall i: int {:trigger intervals[i, 1]} :: (0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1]) && (0 <= i < intervals.Length0 ==> intervals[i, 1] <= 50000)
  modifies intervals
  ensures count >= 0
  decreases intervals
{
  var row := intervals.Length0;
  if row == 0 {
    return 0;
  }
  bubble_sort(intervals);
  var i := 1;
  count := 1;
  var end := intervals[0, 1];
  while i < row
    invariant 1 <= i <= row
    invariant 1 <= count <= i
    invariant intervals[0, 1] <= end <= intervals[i - 1, 1]
    decreases row - i
  {
    if intervals[i, 0] >= end {
      count := count + 1;
      end := intervals[i, 1];
    }
    i := i + 1;
  }
  return row - count;
}

method bubble_sort(a: array2<int>)
  requires a.Length1 == 2
  modifies a
  ensures sorted(a, 0, a.Length0 - 1)
  decreases a
{
  var i := a.Length0 - 1;
  while i > 0
    invariant i < 0 ==> a.Length0 == 0
    invariant sorted(a, i, a.Length0 - 1)
    invariant partitioned(a, i)
    decreases i - 0
  {
    var j := 0;
    while j < i
      invariant 0 < i < a.Length0 && 0 <= j <= i
      invariant sorted(a, i, a.Length0 - 1)
      invariant partitioned(a, i)
      invariant forall k: int {:trigger a[k, 1]} :: 0 <= k <= j ==> a[k, 1] <= a[j, 1]
      decreases i - j
    {
      if a[j, 1] > a[-(j + 1), 1] {
        a[j, 1], a[j + 1, 1] := a[j + 1, 1], a[j, 1];
      }
      j := j + 1;
    }
    i := i - 1;
  }
}

predicate sorted(a: array2<int>, l: int, u: int)
  requires a.Length1 == 2
  reads a
  decreases {a}, a, l, u
{
  forall i: int, j: int {:trigger a[j, 1], a[i, 1]} :: 
    0 <= l <= i <= j <= u < a.Length0 ==>
      a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
  requires a.Length1 == 2
  reads a
  decreases {a}, a, i
{
  forall k: int, k': int {:trigger a[k', 1], a[k, 1]} :: 
    0 <= k <= i < k' < a.Length0 ==>
      a[k, 1] <= a[k', 1]
}
