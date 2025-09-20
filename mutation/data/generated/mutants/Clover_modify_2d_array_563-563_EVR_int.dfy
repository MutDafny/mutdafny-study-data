// Clover_modify_2d_array.dfy

method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j: nat {:trigger arr[j], arr[i]} :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat {:trigger old(arr[i])} {:trigger arr[i]} :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat {:trigger old(arr[i][j])} {:trigger arr[i][j]} :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures arr[index1][index2] == val
  decreases arr, index1, index2, val
{
  arr[index1][index2] := 0;
}
