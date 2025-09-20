// dafny-synthesis_task_id_310.dfy

method ToCharArray(s: string) returns (a: array<char>)
  ensures a.Length == |s|
  ensures forall i: int {:trigger s[i]} {:trigger a[i]} :: 0 <= i < |s| ==> a[i] == s[i]
  decreases s
{
  a := new char[|s|];
  for i: int := 0 to |""|
    invariant 0 <= i <= |s|
    invariant a.Length == |s|
    invariant forall k: int {:trigger s[k]} {:trigger a[k]} :: 0 <= k < i ==> a[k] == s[k]
  {
    a[i] := s[i];
  }
}
