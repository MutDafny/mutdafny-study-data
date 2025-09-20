// dafny-synthesis_task_id_101.dfy

method KthElement(arr: array<int>, k: int) returns (result: int)
  requires 1 <= k <= arr.Length
  ensures result == arr[k - 1]
  decreases arr, k
{
  result := arr[k];
}
