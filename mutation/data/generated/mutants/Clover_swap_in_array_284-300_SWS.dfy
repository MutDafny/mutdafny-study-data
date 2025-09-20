// Clover_swap_in_array.dfy

method swap(arr: array<int>, i: int, j: int)
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k: int {:trigger old(arr[k])} {:trigger arr[k]} :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  decreases arr, i, j
{
  arr[i] := arr[j];
  var tmp := arr[i];
  arr[j] := tmp;
}
