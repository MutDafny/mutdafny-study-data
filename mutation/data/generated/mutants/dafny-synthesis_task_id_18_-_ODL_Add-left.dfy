// dafny-synthesis_task_id_18.dfy

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i: int {:trigger v[i]} :: (0 <= i < |v| ==> v[i] in s1) && (0 <= i < |v| ==> !(v[i] in s2))
  ensures forall i: int {:trigger s1[i]} :: 0 <= i < |s1| ==> s1[i] in s2 || s1[i] in v
  decreases s1, s2
{
  var v': string := [];
  for i: int := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k: int {:trigger v'[k]} :: (0 <= k < |v'| ==> v'[k] in s1) && (0 <= k < |v'| ==> !(v'[k] in s2))
    invariant forall k: int {:trigger s1[k]} :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v'
  {
    if !(s1[i] in s2) {
      v' := [s1[i]];
    }
  }
  return v';
}
