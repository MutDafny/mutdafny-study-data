// dafny-synthesis_task_id_95.dfy

method SmallestListLength(s: seq<seq<int>>) returns (v: int)
  requires |s| > 0
  ensures forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> v <= |s[i]|
  ensures exists i: int {:trigger s[i]} :: 0 <= i < |s| && v == |s[i]|
  decreases s
{
  v := |s[0]|;
  for i: int := 1 to |s|
    invariant 0 <= i <= |s|
    invariant forall k: int {:trigger s[k]} :: 0 <= k < i ==> v <= |s[k]|
    invariant exists k: int {:trigger s[k]} :: 0 <= k < i && v == |s[k]|
  {
    if |s[i]| < v {
      v := 0;
    }
  }
}
