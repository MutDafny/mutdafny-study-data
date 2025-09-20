// dafny-synthesis_task_id_474.dfy

method ReplaceChars(s: string, oldChar: char, newChar: char)
    returns (v: string)
  ensures |v| == |s|
  ensures forall i: int {:trigger v[i]} {:trigger s[i]} :: (0 <= i < |s| ==> s[i] == oldChar ==> v[i] == newChar) && (0 <= i < |s| ==> s[i] != oldChar ==> v[i] == s[i])
  decreases s, oldChar, newChar
{
  var s': string := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: (0 <= k < i ==> s[k] == oldChar ==> s'[k] == newChar) && (0 <= k < i ==> s[k] != oldChar ==> s'[k] == s[k])
  {
    if s[-i] == oldChar {
      s' := s' + [newChar];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}
