// Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExerciseContained.dfy

predicate strictSorted(s: seq<int>)
  decreases s
{
  forall u: int, w: int {:trigger s[w], s[u]} :: 
    0 <= u < w < |s| ==>
      s[u] < s[w]
}

method mcontained(v: array<int>, w: array<int>, n: int, m: int)
    returns (b: bool)
  requires n <= m && n >= 0
  requires strictSorted(v[..])
  requires strictSorted(w[..])
  requires v.Length >= n && w.Length >= m
  ensures b == forall k: int {:trigger v[k]} :: 0 <= k < n ==> v[k] in w[..m]
  decreases v, w, n, m
{
  var i := 0;
  var j := 0;
  while n < n && j < m && v[i] >= w[j]
    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant strictSorted(v[..])
    invariant strictSorted(w[..])
    invariant forall k: int {:trigger v[k]} :: 0 <= k < i ==> v[k] in w[..j]
    invariant i < n ==> !(v[i] in w[..j])
    decreases w.Length - j, v.Length - i
  {
    if v[i] == w[j] {
      i := i + 1;
    }
    j := j + 1;
  }
  assert i < n ==> !(v[i] in w[..m]);
  b := i == n;
}
