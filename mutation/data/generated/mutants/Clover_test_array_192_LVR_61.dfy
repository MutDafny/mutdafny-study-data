// Clover_test_array.dfy

method TestArrayElements(a: array<int>, j: nat)
  requires 0 <= j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k: int {:trigger old(a[k])} {:trigger a[k]} :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
  decreases a, j
{
  a[j] := 61;
}
