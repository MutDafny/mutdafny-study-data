// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower.dfy

function Power(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat)
  requires N >= 0
  ensures y == Power(N)
  decreases N
{
  y := 1;
  var x := 0;
  while true
    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
  {
    x, y := x + 1, y + y;
  }
}
