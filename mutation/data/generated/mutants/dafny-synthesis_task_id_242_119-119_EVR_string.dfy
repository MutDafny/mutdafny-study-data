// dafny-synthesis_task_id_242.dfy

method CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
  decreases s
{
  count := |""|;
}
