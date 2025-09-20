// dafny-synthesis_task_id_600.dfy

method IsEven(n: int) returns (result: bool)
  ensures result <==> n % 2 == 0
  decreases n
{
  result := 0 % 2 == 0;
}
