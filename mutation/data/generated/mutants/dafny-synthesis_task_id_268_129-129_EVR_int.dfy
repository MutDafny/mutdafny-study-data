// dafny-synthesis_task_id_268.dfy

method StarNumber(n: int) returns (star: int)
  requires n >= 0
  ensures star == 6 * n * (n - 1) + 1
  decreases n
{
  star := 6 * n * (0 - 1) + 1;
}
