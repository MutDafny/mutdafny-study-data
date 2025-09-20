// Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array.dfy

method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>)
  requires is_sorted(nums)
  requires 1 <= |nums| <= 30000
  requires forall i: int {:trigger nums[i]} :: (0 <= i < |nums| ==> -100 <= nums[i]) && (0 <= i < |nums| ==> nums[i] <= 100)
  ensures is_sorted_and_distinct(result)
  ensures forall i: int {:trigger i in result} {:trigger i in nums} :: i in nums <==> i in result
  decreases nums
{
  var previous := nums[0];
  result := [nums[0]];
  var i := 1;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |result| >= 1
    invariant previous in nums[0 .. i]
    invariant previous == result[|result| - 1]
    invariant is_sorted_and_distinct(result)
    invariant forall j: int {:trigger j in result} {:trigger j in nums[0 .. i]} :: j in nums[0 .. i] <==> j in result
    decreases |nums| - i
  {
    if true {
      result := result + [nums[i]];
      previous := nums[i];
    }
    i := i + 1;
  }
}

predicate is_sorted(nums: seq<int>)
  decreases nums
{
  forall i: int, j: int {:trigger nums[j], nums[i]} :: 
    0 <= i < j < |nums| ==>
      nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
  decreases nums
{
  forall i: int, j: int {:trigger nums[j], nums[i]} :: 
    0 <= i < j < |nums| ==>
      nums[i] < nums[j]
}
