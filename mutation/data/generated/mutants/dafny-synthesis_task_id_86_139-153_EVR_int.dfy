// dafny-synthesis_task_id_86.dfy

method CenteredHexagonalNumber(n: nat) returns (result: nat)
  requires n >= 0
  ensures result == 3 * n * (n - 1) + 1
  decreases n
{
  result := 0 + 1;
}
