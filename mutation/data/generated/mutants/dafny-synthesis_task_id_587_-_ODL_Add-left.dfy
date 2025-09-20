// dafny-synthesis_task_id_587.dfy

method ArrayToSeq(a: array<int>) returns (s: seq<int>)
  requires a != null
  ensures |s| == a.Length
  ensures forall i: int {:trigger a[i]} {:trigger s[i]} :: 0 <= i < a.Length ==> s[i] == a[i]
  decreases a
{
  s := [];
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |s| == i
    invariant forall j: int {:trigger a[j]} {:trigger s[j]} :: 0 <= j < i ==> s[j] == a[j]
  {
    s := [a[i]];
  }
}
