// dafny-synthesis_task_id_401.dfy

method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| > 0 && |b| > 0
  requires |a| == |b|
  requires forall i: int {:trigger b[i]} {:trigger a[i]} :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i: int {:trigger a[i]} {:trigger result[i]} :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger result[i]} :: 0 <= i < |result| ==> forall j: int {:trigger b[i][j]} {:trigger a[i][j]} {:trigger result[i][j]} :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
  decreases a, b
{
  result := [];
  for i: int := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k: int {:trigger a[k]} {:trigger result[k]} :: 0 <= k < i ==> |result[k]| == |a[k]|
    invariant forall k: int {:trigger b[k]} {:trigger a[k]} {:trigger result[k]} :: 0 <= k < i ==> forall j: int {:trigger b[k][j]} {:trigger a[k][j]} {:trigger result[k][j]} :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
  {
    var subResult := [];
    for j: int := 0 to |a[i]|
      invariant 0 <= j <= |a[i]|
      invariant |subResult| == j
      invariant forall k: int {:trigger b[i][k]} {:trigger a[i][k]} {:trigger subResult[k]} :: 0 <= k < j ==> subResult[k] == a[i][k] + b[i][k]
    {
      subResult := subResult + [0];
    }
    result := result + [subResult];
  }
}
