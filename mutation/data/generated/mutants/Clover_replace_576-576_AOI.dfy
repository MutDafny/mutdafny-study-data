// Clover_replace.dfy

method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i: int {:trigger arr[i]} {:trigger old(arr[i])} :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i: int {:trigger arr[i]} {:trigger old(arr[i])} :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
  decreases arr, k
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j: int {:trigger arr[j]} {:trigger old(arr[j])} :: 0 <= j < i ==> old(arr[j]) > k ==> arr[j] == -1
    invariant forall j: int {:trigger arr[j]} {:trigger old(arr[j])} :: 0 <= j < i ==> old(arr[j]) <= k ==> arr[j] == old(arr[j])
    invariant forall j: int {:trigger arr[j]} {:trigger old(arr[j])} :: i <= j < arr.Length ==> old(arr[j]) == arr[j]
    decreases arr.Length - i
  {
    if arr[i] > -k {
      arr[i] := -1;
    }
    i := i + 1;
  }
}
