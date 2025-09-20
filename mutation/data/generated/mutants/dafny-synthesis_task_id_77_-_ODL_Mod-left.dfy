// dafny-synthesis_task_id_77.dfy

method IsDivisibleBy11(n: int) returns (result: bool)
  ensures result <==> n % 11 == 0
  decreases n
{
  result := 11 == 0;
}
