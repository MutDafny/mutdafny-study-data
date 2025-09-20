// HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Largest Sum_largest_sum.dfy

method largest_sum(nums: array<int>, k: int) returns (sum: int)
  requires nums.Length > 0
  ensures max_sum_subarray(nums, sum, 0, nums.Length)
  decreases nums, k
{
  var max_sum := 0;
  var i := 0;
  var current_sum := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant max_sum_subarray(nums, max_sum, 0, i)
    invariant forall j: int {:trigger Sum_Array(nums, j, i)} :: 0 <= j < i ==> Sum_Array(nums, j, i) <= current_sum
    decreases nums.Length - i
  {
    current_sum := current_sum + nums[i];
    if current_sum > max_sum {
      max_sum := current_sum;
    }
    if current_sum < 0 {
      current_sum := 0;
    }
    i := i + 1;
  }
  return max_sum;
}

predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
  requires arr.Length > 0
  requires 0 <= start <= stop <= arr.Length
  reads arr
  decreases {arr}, arr, sum, start, stop
{
  forall u: int, v: int {:trigger Sum_Array(arr, u, v)} :: 
    start <= u < v <= stop ==>
      Sum_Array(arr, u, v) <= sum
}

function Sum_Array(arr: array<int>, start: int, stop: int): int
  requires 0 <= start <= stop <= arr.Length
  reads arr
  decreases stop - start
{
  if start >= stop then
    0
  else
    arr[stop - 1] + Sum_Array(arr, start, stop - 1)
}
