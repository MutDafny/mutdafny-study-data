// dafny-synthesis_task_id_79.dfy

method IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
  decreases s
{
  result := |s| % 1 == 1;
}
