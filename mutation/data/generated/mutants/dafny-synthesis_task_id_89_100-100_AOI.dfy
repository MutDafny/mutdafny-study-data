// dafny-synthesis_task_id_89.dfy

method ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
  decreases n
{
  m := -n - 1;
}
