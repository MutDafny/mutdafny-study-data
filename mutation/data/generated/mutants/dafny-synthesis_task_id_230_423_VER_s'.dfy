// dafny-synthesis_task_id_230.dfy

method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i: int {:trigger v[i]} {:trigger s[i]} :: (0 <= i < |s| ==> s[i] == ' ' ==> v[i] == ch) && (0 <= i < |s| ==> s[i] != ' ' ==> v[i] == s[i])
  decreases s, ch
{
  var s': string := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: (0 <= k < i ==> s[k] == ' ' ==> s'[k] == ch) && (0 <= k < i ==> s[k] != ' ' ==> s'[k] == s[k])
  {
    if s'[i] == ' ' {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}
