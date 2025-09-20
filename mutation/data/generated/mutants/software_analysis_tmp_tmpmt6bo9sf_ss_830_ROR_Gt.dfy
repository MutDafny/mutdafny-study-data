// software_analysis_tmp_tmpmt6bo9sf_ss.dfy

method find_min_index(a: array<int>, s: int, e: int)
    returns (min_i: int)
  requires a.Length > 0
  requires 0 <= s < a.Length
  requires e <= a.Length
  requires e > s
  ensures min_i >= s
  ensures min_i < e
  ensures forall k: int {:trigger a[k]} :: s <= k < e ==> a[min_i] <= a[k]
  decreases a, s, e
{
  min_i := s;
  var i: int := s;
  while i < e
    invariant s <= i <= e
    invariant s <= min_i < e
    invariant forall k: int {:trigger a[k]} :: s <= k < i ==> a[min_i] <= a[k]
    decreases e - i
  {
    if a[i] <= a[min_i] {
      min_i := i;
    }
    i := i + 1;
  }
}

predicate is_sorted(ss: seq<int>)
  decreases ss
{
  forall i: int, j: int {:trigger ss[j], ss[i]} :: 
    0 <= i <= j < |ss| ==>
      ss[i] <= ss[j]
}

predicate is_permutation(a: seq<int>, b: seq<int>)
  decreases |a|, |b|
{
  |a| > |b| &&
  ((|a| == 0 && |b| == 0) || exists i: int, j: int {:trigger b[0 .. j], a[0 .. i]} {:trigger b[0 .. j], a[i]} {:trigger a[0 .. i], b[j]} {:trigger b[j], a[i]} :: 0 <= i < |a| && 0 <= j < |b| && a[i] == b[j] && is_permutation(a[0 .. i] + if i < |a| then a[i + 1..] else [], b[0 .. j] + if j < |b| then b[j + 1..] else []))
}

predicate is_permutation2(a: seq<int>, b: seq<int>)
  decreases a, b
{
  multiset(a) == multiset(b)
}

method selection_sort(ns: array<int>)
  requires ns.Length >= 0
  modifies ns
  ensures is_sorted(ns[..])
  ensures is_permutation2(old(ns[..]), ns[..])
  decreases ns
{
  var i: int := 0;
  var l: int := ns.Length;
  while i < l
    invariant 0 <= i <= l
    invariant is_permutation2(old(ns[..]), ns[..])
    invariant forall k: int, kk: int {:trigger ns[kk], ns[k]} :: 0 <= k < i && i <= kk < ns.Length ==> ns[k] <= ns[kk]
    invariant is_sorted(ns[..i])
    decreases l - i
  {
    var min_i: int := find_min_index(ns, i, ns.Length);
    ns[i], ns[min_i] := ns[min_i], ns[i];
    i := i + 1;
  }
}
