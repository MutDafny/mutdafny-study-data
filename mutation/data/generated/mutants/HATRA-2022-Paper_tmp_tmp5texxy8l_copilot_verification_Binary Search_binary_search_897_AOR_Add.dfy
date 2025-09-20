// HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Binary Search_binary_search.dfy

method BinarySearch(arr: array<int>, target: int) returns (index: int)
  requires distinct(arr)
  requires sorted(arr)
  ensures -1 <= index < arr.Length
  ensures index == -1 ==> not_found(arr, target)
  ensures index != -1 ==> found(arr, target, index)
  decreases arr, target
{
  var low, high := 0, arr.Length - 1;
  while low <= high
    invariant 0 <= low <= high + 1
    invariant low - 1 <= high < arr.Length
    invariant forall i: int {:trigger arr[i]} :: 0 <= i <= low && high <= i < arr.Length ==> arr[i] != target
    decreases high - low
  {
    var mid := (low + high) / 2;
    if arr[mid] == target {
      return mid;
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid + 1;
    }
  }
  return -1;
}

predicate sorted(a: array<int>)
  reads a
  decreases {a}, a
{
  forall j: int, k: int {:trigger a[k], a[j]} :: 
    0 <= j < k < a.Length ==>
      a[j] <= a[k]
}

predicate distinct(arr: array<int>)
  reads arr
  decreases {arr}, arr
{
  forall i: int, j: int {:trigger arr[j], arr[i]} :: 
    0 <= i < arr.Length &&
    0 <= j < arr.Length ==>
      arr[i] != arr[j]
}

predicate not_found(arr: array<int>, target: int)
  reads arr
  decreases {arr}, arr, target
{
  forall j: int {:trigger arr[j]} :: 
    0 <= j < arr.Length ==>
      arr[j] != target
}

predicate found(arr: array<int>, target: int, index: int)
  requires -1 <= index < arr.Length
  reads arr
  decreases {arr}, arr, target, index
{
  if index == -1 then
    false
  else if arr[index] == target then
    true
  else
    false
}
