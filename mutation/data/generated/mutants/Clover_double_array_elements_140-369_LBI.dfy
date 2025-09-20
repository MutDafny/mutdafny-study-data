// Clover_double_array_elements.dfy

method double_array_elements(s: array<int>)
  modifies s
  ensures forall i: int {:trigger old(s[i])} {:trigger s[i]} :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
  decreases s
{
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall x: int {:trigger old(s[x])} {:trigger s[x]} :: i <= x < s.Length ==> s[x] == old(s[x])
    invariant forall x: int {:trigger old(s[x])} {:trigger s[x]} :: 0 <= x < i ==> s[x] == 2 * old(s[x])
    decreases s.Length - i
  {
    break;
    s[i] := 2 * s[i];
    i := i + 1;
  }
}
