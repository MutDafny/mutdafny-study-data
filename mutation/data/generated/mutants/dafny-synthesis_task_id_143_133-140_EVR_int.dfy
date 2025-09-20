// dafny-synthesis_task_id_143.dfy

method CountArrays(arrays: seq<array<int>>) returns (count: int)
  ensures count >= 0
  ensures count == |arrays|
  decreases arrays
{
  count := 0;
}
