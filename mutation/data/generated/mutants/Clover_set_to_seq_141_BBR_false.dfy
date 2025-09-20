// Clover_set_to_seq.dfy

method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
  decreases s
{
  xs := [];
  var left: set<T> := s;
  while false
    invariant multiset(left) + multiset(xs) == multiset(s)
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
  }
}
