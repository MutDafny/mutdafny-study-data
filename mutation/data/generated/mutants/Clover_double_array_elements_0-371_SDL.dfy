// Clover_double_array_elements.dfy

method double_array_elements(s: array<int>)
  modifies s
  ensures forall i: int {:trigger old(s[i])} {:trigger s[i]} :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
  decreases s
{
}
