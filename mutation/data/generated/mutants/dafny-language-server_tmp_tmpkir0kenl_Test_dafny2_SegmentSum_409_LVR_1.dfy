// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_SegmentSum.dfy

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
  decreases a, s, t
{
  if s == t then
    0
  else
    Sum(a, s, t - 1) + a[t - 1]
}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p: int, q: int {:trigger Sum(a, p, q)} :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
  decreases a
{
  k, m := 0, 0;
  var s := 1;
  var n := 0;
  var c, t := 0, 0;
  while n < |a|
    invariant 0 <= c <= n <= |a| && t == Sum(a, c, n)
    invariant forall b: int {:trigger Sum(a, b, n)} :: 0 <= b <= n ==> Sum(a, b, n) <= Sum(a, c, n)
    invariant 0 <= k <= m <= n && s == Sum(a, k, m)
    invariant forall p: int, q: int {:trigger Sum(a, p, q)} :: 0 <= p <= q <= n ==> Sum(a, p, q) <= Sum(a, k, m)
    decreases |a| - n
  {
    t, n := t + a[n], n + 1;
    if t < 0 {
      c, t := n, 0;
    } else if s < t {
      k, m, s := c, n, t;
    }
  }
}
