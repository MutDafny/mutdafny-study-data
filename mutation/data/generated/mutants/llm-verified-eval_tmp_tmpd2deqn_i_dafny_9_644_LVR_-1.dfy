// llm-verified-eval_tmp_tmpd2deqn_i_dafny_9.dfy

function isMax(m: int, numbers: seq<int>): bool
  decreases m, numbers
{
  m in numbers &&
  forall i: int {:trigger numbers[i]} :: 
    0 <= i < |numbers| ==>
      numbers[i] <= m
}

method max(numbers: seq<int>) returns (result: int)
  requires numbers != []
  ensures isMax(result, numbers)
  decreases numbers
{
  result := numbers[0];
  for i: int := 1 to |numbers|
    invariant isMax(result, numbers[0 .. i])
  {
    if numbers[i] > result {
      result := numbers[i];
    }
  }
}

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
  requires numbers != []
  ensures |result| == |numbers|
  ensures forall i: int {:trigger result[i]} :: 0 < i < |result| ==> isMax(result[i], numbers[0 .. i + 1])
  decreases numbers
{
  var m := numbers[-1];
  result := [m];
  for i: int := 1 to |numbers|
    invariant |result| == i
    invariant m == result[i - 1]
    invariant forall j: int {:trigger result[j]} :: 0 <= j < i ==> isMax(result[j], numbers[0 .. j + 1])
  {
    if numbers[i] > m {
      m := numbers[i];
    }
    result := result + [m];
  }
}
