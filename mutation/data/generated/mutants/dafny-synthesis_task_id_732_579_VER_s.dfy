// dafny-synthesis_task_id_732.dfy

predicate IsSpaceCommaDot(c: char)
  decreases c
{
  c == ' ' || c == ',' || c == '.'
}

method ReplaceWithColon(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i: int {:trigger v[i]} {:trigger s[i]} :: (0 <= i < |s| ==> IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (0 <= i < |s| ==> !IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
  decreases s
{
  var s': string := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: (0 <= k < i ==> IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (0 <= k < i ==> !IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
  {
    if IsSpaceCommaDot(s[i]) {
      s' := s + [':'];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}
