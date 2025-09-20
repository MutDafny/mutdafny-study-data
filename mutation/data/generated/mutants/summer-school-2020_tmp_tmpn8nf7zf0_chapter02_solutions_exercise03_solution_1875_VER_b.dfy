// summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise03_solution.dfy

predicate IsSorted(s: seq<int>)
  decreases s
{
  forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == i + 1 :: 
    0 <= i &&
    i < |s| - 1 ==>
      s[i] <= s[_t#0]
}

predicate SortSpec(input: seq<int>, output: seq<int>)
  decreases input, output
{
  IsSorted(output) &&
  multiset(output) == multiset(input)
}

method merge_sort(input: seq<int>) returns (output: seq<int>)
  ensures SortSpec(input, output)
  decreases input
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    assert left + right == input;
  }
}

method merge(a: seq<int>, b: seq<int>) returns (output: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a + b, output)
  decreases a, b
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant 0 < |output| && ai < |a| ==> output[|output| - 1] <= a[ai]
    invariant 0 < |output| && bi < |b| ==> output[|output| - 1] <= b[bi]
    invariant forall i: int, _t#0: int {:trigger output[_t#0], output[i]} | _t#0 == i + 1 :: 0 <= i && i < |output| - 1 ==> output[i] <= output[_t#0]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    decreases |a| - ai + |b| - bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && b[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
      assert b[bo .. bi] == [b[bo]];
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
      assert a[ao .. ai] == [a[ao]];
    }
    assert a[..ai] == a[..ao] + a[ao .. ai];
    assert b[..bi] == b[..bo] + b[bo .. bi];
  }
  assert a == a[..ai];
  assert b == b[..bi];
}

method fast_sort(input: seq<int>) returns (output: seq<int>)
  decreases input
{
  output := [1, 2, 3];
}
