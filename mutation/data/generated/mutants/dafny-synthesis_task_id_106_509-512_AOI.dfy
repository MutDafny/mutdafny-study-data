// dafny-synthesis_task_id_106.dfy

method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
  requires a != null
  ensures |r| == |s| + a.Length
  ensures forall i: int {:trigger s[i]} {:trigger r[i]} :: 0 <= i < |s| ==> r[i] == s[i]
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
  decreases s, a
{
  r := s;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |r| == |s| + i
    invariant forall j: int {:trigger s[j]} {:trigger r[j]} :: 0 <= j < |s| ==> r[j] == s[j]
    invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> r[|s| + j] == a[j]
  {
    r := r + [-a[i]];
  }
}
