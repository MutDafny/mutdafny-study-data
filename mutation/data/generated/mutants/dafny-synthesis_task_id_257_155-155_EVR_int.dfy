// dafny-synthesis_task_id_257.dfy

method Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
  decreases a, b
{
  result := [b, 0];
}
