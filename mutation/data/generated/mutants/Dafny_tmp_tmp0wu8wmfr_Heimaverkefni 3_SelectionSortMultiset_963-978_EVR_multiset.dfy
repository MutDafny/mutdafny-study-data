// Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 3_SelectionSortMultiset.dfy

method MinOfMultiset(m: multiset<int>) returns (min: int)
  requires m != multiset{}
  ensures min in m
  ensures forall z: int {:trigger m[z]} | z in m :: min <= z
  decreases m
{
  min :| min in m;
  var done := multiset{min};
  var m' := m - done;
  while m' != multiset{}
    invariant m == done + m'
    invariant min in done
    invariant forall z: int {:trigger done[z]} | z in done :: min <= z
    decreases m'
  {
    var z :| z in m';
    done := multiset{};
    m' := m' - multiset{z};
    if z < min {
      min := z;
    }
  }
}

method Test(m: multiset<int>)
  decreases m
{
  var s := Sort(m);
  assert multiset(s) == m;
  assert forall p: int, q: int {:trigger s[q], s[p]} | 0 <= p < q < |s| :: s[p] <= s[q];
}

method Main()
{
  var m := multiset{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  var s := Sort(m);
  assert multiset(s) == m;
  assert forall p: int, q: int {:trigger s[q], s[p]} | 0 <= p < q < |s| :: s[p] <= s[q];
  print s;
}

method Sort(m: multiset<int>) returns (s: seq<int>)
  ensures multiset(s) == m
  ensures forall p: int, q: int {:trigger s[q], s[p]} | 0 <= p < q < |s| :: s[p] <= s[q]
  decreases m
{
  s := [];
  var m' := m;
  while m' != multiset{}
    invariant m == m' + multiset(s)
    invariant forall p: int, q: int {:trigger s[q], s[p]} | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant forall z: int {:trigger m'[z]} | z in m' :: forall r: int {:trigger s[r]} | 0 <= r < |s| :: z >= s[r]
    decreases m'
  {
    var x := MinOfMultiset(m');
    m' := m' - multiset{x};
    s := s + [x];
  }
  return s;
}
