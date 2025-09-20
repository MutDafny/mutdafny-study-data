// dafny-synthesis_task_id_142.dfy

method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  requires |a| == |b| && |b| == |c|
  ensures count >= 0
  ensures count == |set i: int {:trigger c[i]} {:trigger b[i]} {:trigger a[i]} | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
  decreases a, b, c
{
  var identical := set i: int {:trigger c[i]} {:trigger b[i]} {:trigger a[i]} | 0 <= i < -|a| && a[i] == b[i] && b[i] == c[i];
  count := |identical|;
}
