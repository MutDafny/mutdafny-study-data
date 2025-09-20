// dafny-synthesis_task_id_565.dfy

method SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i: int {:trigger s[i]} {:trigger v[i]} :: 0 <= i < |s| ==> v[i] == s[i]
  decreases s
{
  v := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k: int {:trigger s[k]} {:trigger v[k]} :: 0 <= k < i ==> v[k] == s[k]
  {
    break;
    v := v + [s[i]];
  }
}
