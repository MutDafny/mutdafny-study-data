// Dafny-Grind75_tmp_tmpsxfz3i4r_problems_twoSum.dfy

predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
  requires i < |nums|
  requires j < |nums|
  decreases i, j, nums, target
{
  i != j &&
  nums[i] + nums[j] == target
}

method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
  requires exists i: nat, j: nat {:trigger summingPair(i, j, nums, target)} :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat {:trigger summingPair(l, m, nums, target)} :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
  ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
  decreases nums, target
{
  pair := (0, 0);
  var i: nat := 0;
  while i < |nums|
    invariant i <= |nums|
    invariant forall z: nat, j: nat {:trigger summingPair(z, j, nums, target)} :: 0 <= z < i && z + 1 <= j < |nums| ==> !summingPair(z, j, nums, target)
    decreases |nums| - i
  {
    var k: nat := i + 1;
    while k < |nums|
      invariant i + 1 <= k <= |nums|
      invariant forall q: nat {:trigger summingPair(i, q, nums, target)} :: i + 1 <= q < k <= |nums| ==> !summingPair(i, q, nums, target)
      decreases |nums| - k
    {
      k := k + 1;
    }
    i := i + 1;
  }
}
