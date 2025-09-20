// dafny-synthesis_task_id_307.dfy

method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
  ensures |copy| == |s|
  ensures forall i: int {:trigger s[i]} {:trigger copy[i]} :: 0 <= i < |s| ==> copy[i] == s[i]
  decreases s
{
  var newSeq: seq<int> := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |newSeq| == i
    invariant forall k: int {:trigger s[k]} {:trigger newSeq[k]} :: 0 <= k < i ==> newSeq[k] == s[k]
  {
    newSeq := newSeq + [s[i]];
  }
  return [];
}
