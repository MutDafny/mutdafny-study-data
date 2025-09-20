// dafny-synthesis_task_id_618.dfy

method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  requires forall i: int {:trigger b[i]} :: 0 <= i < |b| ==> b[i] != 0
  ensures |result| == |a|
  ensures forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger result[i]} :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
  decreases a, b
{
  result := [1, 2, 3];
  for i: int := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k: int {:trigger b[k]} {:trigger a[k]} {:trigger result[k]} :: 0 <= k < i ==> result[k] == a[k] / b[k]
  {
    result := result + [a[i] / b[i]];
  }
}
