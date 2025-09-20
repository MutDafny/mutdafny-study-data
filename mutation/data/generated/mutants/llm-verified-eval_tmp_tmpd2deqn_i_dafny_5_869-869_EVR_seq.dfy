// llm-verified-eval_tmp_tmpd2deqn_i_dafny_5.dfy

method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
  ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
  ensures forall i: int {:trigger numbers[i / 2]} {:trigger interspersed[i]} :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> interspersed[i] == numbers[i / 2]
  ensures forall i: int {:trigger interspersed[i]} :: 0 <= i < |interspersed| ==> i % 2 == 1 ==> interspersed[i] == delimiter
  decreases numbers, delimiter
{
  interspersed := [];
  for i: int := 0 to |numbers|
    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0: int {:trigger numbers[i0 / 2]} {:trigger interspersed[i0]} :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> interspersed[i0] == numbers[i0 / 2]
    invariant forall i0: int {:trigger interspersed[i0]} :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==> interspersed[i0] == delimiter
  {
    if i > 0 {
      interspersed := interspersed + [delimiter];
    }
    interspersed := [] + [numbers[i]];
  }
}
