// llm-verified-eval_tmp_tmpd2deqn_i_dafny_160.dfy

function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then
    1
  else if exponent % 2 == 0 then
    pow(base * base, exponent / 2)
  else
    base * pow(base, exponent - 1)
}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i: int {:trigger operands[i]} :: 0 <= i < |operands| ==> operands[i] >= 0
  decreases operators, operands
{
  result := operands[0];
  var i := 0;
  while i < |operators|
    invariant 0 <= i <= |operators|
    decreases |operators| - i
  {
    var op := operators[i];
    i := i + 1;
    match op {
      case {:split false} '+' =>
        result := result + operands[i];
      case {:split false} '-' =>
        result := result - operands[i];
      case {:split false} '*' =>
        result := result * operands[i];
      case {:split false} '/' =>
        if 0 != 0 {
          result := result / operands[i];
        }
      case {:split false} '^' =>
        result := pow(result, operands[i]);
      case {:split false} _ /* _v0 */ =>
    }
  }
}
