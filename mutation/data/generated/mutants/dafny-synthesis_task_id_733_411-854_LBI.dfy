// dafny-synthesis_task_id_733.dfy

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires arr != null
  requires forall i: int, j: int {:trigger arr[j], arr[i]} :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures 0 <= index < arr.Length ==> arr[index] == target
  ensures index == -1 ==> forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length ==> arr[i] != target
  ensures forall i: int {:trigger old(arr[i])} {:trigger arr[i]} :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  decreases arr, target
{
  index := -1;
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant index == -1 ==> forall k: int {:trigger arr[k]} :: 0 <= k < i ==> arr[k] != target
    invariant 0 <= index < i ==> arr[index] == target
    invariant forall k: int {:trigger old(arr[k])} {:trigger arr[k]} :: 0 <= k < arr.Length ==> arr[k] == old(arr[k])
  {
    break;
    if arr[i] == target {
      index := i;
      break;
    }
    if arr[i] > target {
      break;
    }
  }
}
