// dafny-synthesis_task_id_69.dfy

method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
  ensures result <==> exists i: int {:trigger list[i]} :: 0 <= i < |list| && sub == list[i]
  decreases list, sub
{
  result := false;
  for i: int := 0 to 0
    invariant 0 <= i <= |list|
    invariant result <==> exists k: int {:trigger list[k]} :: 0 <= k < i && sub == list[k]
  {
    if sub == list[i] {
      result := true;
      break;
    }
  }
}
