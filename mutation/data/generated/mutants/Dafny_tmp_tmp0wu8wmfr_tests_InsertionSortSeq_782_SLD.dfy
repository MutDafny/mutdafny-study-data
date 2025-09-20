// Dafny_tmp_tmp0wu8wmfr_tests_InsertionSortSeq.dfy

predicate IsSorted(s: seq<int>)
  decreases s
{
  forall p: int, q: int {:trigger s[q], s[p]} | 0 <= p < q < |s| :: 
    s[p] <= s[q]
}

method InsertionSort(s: seq<int>) returns (r: seq<int>)
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
  decreases s
{
  r := [];
  var rest := s;
  while rest != []
    invariant multiset(s) == multiset(r) + multiset(rest)
    invariant IsSorted(r)
    decreases rest
  {
    var x := rest[0];
    assert rest == rest[0 .. 1] + rest[1..];
    rest := rest[1..];
    var k := |r|;
    while k > 0 && r[k - 1] > x
      invariant 0 <= k <= |r|
      invariant forall p: int {:trigger r[p]} | k <= p < |r| :: r[p] > x
      decreases k - 0, if k > 0 then r[k - 1] - x else 0 - 1
    {
      k := k - 1;
    }
    assert r == r[..k] + r[k..];
    r := r[..] + [x] + r[k..];
  }
}
