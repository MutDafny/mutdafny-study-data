// dafny-synthesis_task_id_424.dfy

method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
  requires forall i: int {:trigger l[i]} :: 0 <= i < |l| ==> |l[i]| > 0
  ensures |r| == |l|
  ensures forall i: int {:trigger l[i]} {:trigger r[i]} :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
  decreases l
{
  var rearChars: seq<char> := [];
  for i: int := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |rearChars| == i
    invariant forall k: int {:trigger l[k]} {:trigger rearChars[k]} :: 0 <= k < i ==> rearChars[k] == l[k][|l[k]| - 1]
  {
    rearChars := rearChars + [l[i][|l[i]| - 1]];
  }
  return [];
}
