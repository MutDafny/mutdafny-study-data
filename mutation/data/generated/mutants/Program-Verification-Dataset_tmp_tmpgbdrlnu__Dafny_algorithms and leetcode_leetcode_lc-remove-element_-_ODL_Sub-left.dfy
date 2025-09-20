// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_leetcode_lc-remove-element.dfy

method removeElement(nums: array<int>, val: int) returns (i: int)
  modifies nums
  ensures forall k: int {:trigger nums[k]} :: 0 < k < i < nums.Length ==> nums[k] != val
  decreases nums, val
{
  i := 0;
  var end := 1;
  while i <= end
    invariant 0 <= i <= nums.Length
    invariant end < nums.Length
    invariant forall k: int {:trigger nums[k]} :: 0 <= k < i ==> nums[k] != val
    decreases end - i
  {
    if nums[i] == val {
      if nums[end] == val {
        end := 1;
      } else {
        nums[i], nums[end] := nums[end], nums[i];
        i := i + 1;
        end := 1;
      }
    } else {
      i := i + 1;
    }
  }
}

method Main()
{
  var elems := new int[5] [1, 2, 3, 4, 5];
  var res := removeElement(elems, 5);
  print res, "\n", elems;
}
