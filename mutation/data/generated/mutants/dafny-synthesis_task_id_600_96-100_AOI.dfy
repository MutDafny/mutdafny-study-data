// dafny-synthesis_task_id_600.dfy

method IsEven(n: int) returns (result: bool)
  ensures result <==> n % 2 == 0
  decreases n
{
  result := -(n % 2) == 0;
}
