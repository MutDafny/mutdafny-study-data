// Clover_update_array.dfy

method UpdateElements(a: array<int>)
  requires a.Length >= 8
  modifies a
  ensures old(a[4]) + 3 == a[4]
  ensures a[7] == 516
  ensures forall i: int {:trigger old(a[i])} {:trigger a[i]} :: 0 <= i < a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i])
  decreases a
{
  a[4] := a[4] + 3;
  a[7] := 515;
}
