// Clover_remove_front.dfy

method remove_front(a: array<int>) returns (c: array<int>)
  requires a.Length > 0
  ensures a[1..] == c[..]
  decreases a
{
  c := new int[a.Length - 1];
  var i := 1;
  while i != a.Length
    invariant 1 <= i <= a.Length
    invariant forall ii: int {:trigger a[ii]} :: 1 <= ii < i ==> c[ii - 1] == a[ii]
    decreases if i <= a.Length then a.Length - i else i - a.Length
  {
    c[i - 1] := a[i];
    i := i + 1;
  }
}
