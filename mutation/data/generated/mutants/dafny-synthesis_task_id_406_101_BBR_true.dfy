// dafny-synthesis_task_id_406.dfy

method IsOdd(n: int) returns (result: bool)
  ensures result <==> n % 2 == 1
  decreases n
{
  result := true;
}
