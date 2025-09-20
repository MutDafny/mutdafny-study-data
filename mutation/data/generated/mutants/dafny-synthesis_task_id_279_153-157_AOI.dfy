// dafny-synthesis_task_id_279.dfy

method NthDecagonalNumber(n: int) returns (decagonal: int)
  requires n >= 0
  ensures decagonal == 4 * n * n - 3 * n
  decreases n
{
  decagonal := 4 * n * n - -(3 * n);
}
