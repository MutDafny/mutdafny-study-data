// Clover_array_copy.dfy

method iter_copy<T(0)>(s: array<T>) returns (t: array<T>)
  ensures s.Length == t.Length
  ensures forall i: int {:trigger t[i]} {:trigger s[i]} :: 0 <= i < s.Length ==> s[i] == t[i]
  decreases s
{
  t := new T[s.Length];
  var i := 0;
  while true
    invariant 0 <= i <= s.Length
    invariant forall x: int {:trigger t[x]} {:trigger s[x]} :: 0 <= x < i ==> s[x] == t[x]
  {
    t[i] := s[i];
    i := i + 1;
  }
}
