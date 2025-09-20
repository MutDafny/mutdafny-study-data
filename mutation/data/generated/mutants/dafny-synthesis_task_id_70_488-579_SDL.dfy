// dafny-synthesis_task_id_70.dfy

method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
  ensures result <==> forall i: int, j: int {:trigger sequences[j], sequences[i]} :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
  decreases sequences
{
  if |sequences| == 0 {
    return true;
  }
  var firstLength := |sequences[0]|;
  result := true;
  for i: int := 1 to |sequences|
    invariant 1 <= i <= |sequences|
    invariant result <==> forall k: int {:trigger sequences[k]} :: 0 <= k < i ==> |sequences[k]| == firstLength
  {
  }
}
