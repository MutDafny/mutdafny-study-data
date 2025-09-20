// Software-Verification_tmp_tmpv4ueky2d_Remove Element_remove_element.dfy

method remove_element(nums: array<int>, val: int) returns (i: int)
  requires 0 <= nums.Length <= 100
  requires forall i: int {:trigger nums[i]} :: (0 <= i < nums.Length ==> 0 <= nums[i]) && (0 <= i < nums.Length ==> nums[i] <= 50)
  requires 0 <= val <= 100
  modifies nums
  ensures forall j: int {:trigger nums[j]} :: 0 < j < i < nums.Length ==> nums[j] != val
  decreases nums, val
{
  i := 0;
  var end := nums.Length - 1;
  while i <= end
    invariant 0 <= i <= nums.Length
    invariant end < nums.Length
    invariant forall k: int {:trigger nums[k]} :: 0 <= k < i ==> nums[k] != val
    decreases end - i
  {
    if nums[i] == val {
      if nums[end] == val {
        end := end - 1;
      } else {
        nums[i] := nums[i];
        i := i + 1;
        end := end - 1;
      }
    } else {
      i := i + 1;
    }
  }
}
