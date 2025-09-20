// dafny-exercises_tmp_tmp5mvrowrx_leetcode_26-remove-duplicates-from-sorted-array.dfy

method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  requires forall i: int, j: int {:trigger nums[j], nums[i]} | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  modifies nums
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i: int, j: int {:trigger nums[j], nums[i]} | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i: int {:trigger nums[i]} | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i: int {:trigger old(nums[i])} | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
  decreases nums
{
  if nums.Length <= 1 {
    return nums.Length;
  }
  var last := 0;
  var i := 1;
  ghost var nums_before := nums[..];
  while i < nums.Length
    invariant 0 <= last < i <= nums.Length
    invariant nums[i..] == nums_before[i..]
    invariant forall j: int, k: int {:trigger nums[k], nums[j]} | 0 <= j < k <= last :: nums[j] < nums[k]
    invariant forall j: int {:trigger nums[j]} | 0 <= j <= last :: nums[j] in nums_before[..i]
    invariant forall j: int {:trigger nums_before[j]} | 0 <= j < i :: nums_before[j] in nums[..last + 1]
    decreases nums.Length - i
  {
    if nums[last] < nums[i] {
      last := last + 1;
      nums[last] := nums[i];
      assert forall j: int {:trigger nums_before[j]} | 0 <= j < i :: nums_before[j] in nums[..last];
      assert forall j: int {:trigger nums_before[j]} | 0 <= j <= i :: nums_before[j] in nums[..last + 1];
    }
    i := i + 1;
  }
  return last + 1;
}

method Testing()
{
}

method Main()
{
  Testing();
}
