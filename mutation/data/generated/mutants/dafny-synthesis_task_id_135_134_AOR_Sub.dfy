// dafny-synthesis_task_id_135.dfy

method NthHexagonalNumber(n: int) returns (hexNum: int)
  requires n >= 0
  ensures hexNum == n * (2 * n - 1)
  decreases n
{
  hexNum := n - (2 * n - 1);
}
