// Clover_set_to_seq.dfy

method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
  decreases s
{
  var left: set<T> := s;
  xs := [];
  while left != {}
    invariant multiset(left) + multiset(xs) == multiset(s)
    decreases left
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
  }
}
