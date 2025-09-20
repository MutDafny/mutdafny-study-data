// Software-Verification_tmp_tmpv4ueky2d_Contains Duplicate_contains_duplicate.dfy

method contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i: int {:trigger nums[i]} :: (0 <= i < |nums| ==> -1000000000 <= nums[i]) && (0 <= i < |nums| ==> nums[i] <= 1000000000)
  ensures result <==> distinct(nums)
  decreases nums
{
  var i := 0;
  var s: set<int> := {};
  while i < |nums|
    invariant i <= |nums|
    invariant forall j: int {:trigger j in s} {:trigger j in nums[..i]} :: j in nums[..i] <==> j in s
    invariant distinct(nums[..i])
    decreases |nums| - i
  {
    var num := nums[i];
    if num in s {
      return false;
    }
    s := s * {num};
    i := i + 1;
  }
  return true;
}

predicate distinct(nums: seq<int>)
  decreases nums
{
  forall i: int, j: int {:trigger nums[j], nums[i]} :: 
    0 <= i < j < |nums| ==>
      nums[i] != nums[j]
}
