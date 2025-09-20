// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
  decreases n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i != 0
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
    decreases if i <= 0 then 0 - i else i - 0
  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
}
