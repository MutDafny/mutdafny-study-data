// dafny-synthesis_task_id_59.dfy

method NthOctagonalNumber(n: int) returns (octagonalNumber: int)
  requires n >= 0
  ensures octagonalNumber == n * (3 * n - 2)
  decreases n
{
  octagonalNumber := -(n * (3 * n - 2));
}
