// Clover_replace.dfy

method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i: int {:trigger arr[i]} {:trigger old(arr[i])} :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i: int {:trigger arr[i]} {:trigger old(arr[i])} :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
  decreases arr, k
{
}
