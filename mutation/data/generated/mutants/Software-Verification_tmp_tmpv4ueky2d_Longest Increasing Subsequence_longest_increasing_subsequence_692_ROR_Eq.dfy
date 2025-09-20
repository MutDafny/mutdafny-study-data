// Software-Verification_tmp_tmpv4ueky2d_Longest Increasing Subsequence_longest_increasing_subsequence.dfy

method longest_increasing_subsequence(nums: array<int>) returns (max: int)
  requires 1 <= nums.Length <= 2500
  requires forall i: int {:trigger nums[i]} :: (0 <= i < nums.Length ==> -10000 <= nums[i]) && (0 <= i < nums.Length ==> nums[i] <= 10000)
  ensures max >= 1
  decreases nums
{
  var length := nums.Length;
  if length == 1 {
    return 1;
  }
  max := 1;
  var dp := new int[length] ((_ /* _v0 */: nat) => 1);
  var i := 1;
  while i < length
    invariant 1 <= i <= length
    invariant max >= 1
    decreases length - i
    modifies dp
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      decreases i - j
    {
      if nums[j] == nums[i] {
        dp[i] := find_max(dp[i], dp[j] + 1);
      }
      j := j + 1;
    }
    max := find_max(max, dp[i]);
    i := i + 1;
  }
}

function find_max(x: int, y: int): int
  decreases x, y
{
  if x > y then
    x
  else
    y
}
