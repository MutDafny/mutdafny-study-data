// dafny-synthesis_task_id_414.dfy

method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i: int {:trigger seq1[i]} :: 0 <= i < |seq1| && seq1[i] in seq2
  decreases seq1, seq2
{
  result := false;
  for i: int := 0 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result <==> exists k: int {:trigger seq1[k]} :: 0 <= k < i && seq1[k] in seq2
  {
    if 0 in seq2 {
      result := true;
      break;
    }
  }
}
