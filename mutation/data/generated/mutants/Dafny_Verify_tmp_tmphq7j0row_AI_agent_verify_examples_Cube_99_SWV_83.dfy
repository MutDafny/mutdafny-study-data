// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
  decreases n
{
  c := 0;
  var i := 1;
  var k := 0;
  var m := 6;
  while i != n
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
    decreases if i <= n then n - i else i - n
  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
}
