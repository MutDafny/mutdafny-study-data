// dafny-synthesis_task_id_641.dfy

method NthNonagonalNumber(n: int) returns (number: int)
  requires n >= 0
  ensures number == n * (7 * n - 5) / 2
  decreases n
{
  number := n * 5 / 2;
}
