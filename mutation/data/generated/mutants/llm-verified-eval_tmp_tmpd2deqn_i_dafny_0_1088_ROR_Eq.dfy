// llm-verified-eval_tmp_tmpd2deqn_i_dafny_0.dfy

function abs(x: real): real
  decreases x
{
  if x < 0.0 then
    -x
  else
    x
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
  ensures result <==> exists i: int, j: int {:trigger numbers[j], numbers[i]} :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
  ensures result ==> |numbers| > 1
  decreases numbers, threshold
{
  result := false;
  assert forall i0: int {:trigger numbers[i0]} :: 0 <= i0 < 0 ==> forall j0: int {:trigger numbers[j0]} :: 0 <= j0 < |numbers| ==> abs(numbers[i0] - numbers[j0]) >= threshold;
  for i: int := 0 to |numbers|
    invariant forall i0: int {:trigger numbers[i0]} :: 0 <= i0 < i ==> forall j0: int {:trigger numbers[j0]} :: 0 <= j0 < |numbers| ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
  {
    for j: int := 0 to |numbers|
      invariant forall i0: int {:trigger numbers[i0]} :: 0 <= i0 <= i ==> forall j0: int {:trigger numbers[j0]} :: 0 <= j0 < j ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    {
      if i != j && abs(numbers[i] - numbers[j]) == threshold {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}
