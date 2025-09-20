// VerifiedMergeSortDafny_tmp_tmpva7qms1b_MergeSort.dfy

method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| + |a2| == end - start + 1
  modifies b
  ensures sorted_slice(b, start, end)
  decreases a1, a2, start, end, b
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while false
    invariant 0 <= k && k <= end
    invariant sorted_slice(b, start, k)
    invariant |a1| - a1Pos + |a2| - a2Pos == end - k + 1
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant forall i: int {:trigger b[i]} :: start <= i < k && a1Pos < |a1| ==> b[i] <= a1[a1Pos]
    invariant forall i: int {:trigger b[i]} :: start <= i < k && a2Pos < |a2| ==> b[i] <= a2[a2Pos]
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      assert a2Pos >= |a2|;
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      assert a1Pos >= |a1|;
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  requires b.Length == |a2| + |a1|
  modifies b
  ensures sorted_slice(b, start, end)
  ensures merged(a1, a2, b, start, end)
  decreases a1, a2, start, end, b
{
  assert forall xs: seq<int> {:trigger |xs|} :: xs[0 .. |xs|] == xs;
  assert forall xs: seq<int>, a: int, b: int, _t#0: int {:trigger xs[a .. b], xs[a .. _t#0]} | _t#0 == b + 1 :: 0 <= a && a < b && b < |xs| ==> xs[a .. _t#0] == xs[a .. b] + [xs[b]];
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
    invariant 0 <= k && k <= end
    invariant sorted_slice(b, start, k)
    invariant |a1| - a1Pos + |a2| - a2Pos == end - k
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant forall i: int {:trigger b[i]} :: start <= i < k && a1Pos < |a1| ==> b[i] <= a1[a1Pos]
    invariant forall i: int {:trigger b[i]} :: start <= i < k && a2Pos < |a2| ==> b[i] <= a2[a2Pos]
    invariant merged(a1[0 .. a1Pos], a2[0 .. a2Pos], b, start, k)
    decreases end - k
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      assert a2Pos >= |a2|;
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      assert a1Pos >= |a1|;
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  requires end - start == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
  reads b
  decreases {b}, a1, a2, b, start, end
{
  multiset(a1) + multiset(a2) == multiset(b[start .. end])
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
  decreases {a}, a, start, end
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    start <= i <= j < end ==>
      a[i] <= a[j]
}

predicate sorted_seq(a: seq<int>)
  decreases a
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    0 <= i <= j < |a| ==>
      a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
  decreases {a}, a
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}
