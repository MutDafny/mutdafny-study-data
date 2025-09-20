// dafny-synthesis_task_id_435.dfy

method LastDigit(n: int) returns (d: int)
  requires n >= 0
  ensures 0 <= d < 10
  ensures n % 10 == d
  decreases n
{
  d := n - 10;
}
