// dafleet_tmp_tmpa2e4kb9v_0001-0050_0001-two-sum.dfy

ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int)
  decreases pair, nums, target
{
  var (i: int, j: int) := pair;
  0 <= i < |nums| &&
  0 <= j < |nums| &&
  i != j &&
  nums[i] + nums[j] == target
}

method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i: int, j: int {:trigger (i, j)} :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
  decreases nums, target
{
  var e_to_i := map[];
  for j: int := 0 to |nums|
    invariant forall i': int {:trigger nums[i']} | 0 <= i' < j :: nums[i'] in e_to_i
    invariant forall e: int {:trigger e_to_i[e]} {:trigger e in e_to_i} | e in e_to_i :: 0 <= e_to_i[e] && e_to_i[e] < j && nums[e_to_i[e]] == e
    invariant forall i': int, j': int {:trigger (i', j')} | i' < j && j' < j :: !correct_pair((i', j'), nums, target)
  {
    var element := nums[j];
    var rest := target - element;
    if rest in e_to_i {
      var i := e_to_i[rest];
      return (i, j);
    } else {
      e_to_i := map[];
    }
  }
}
