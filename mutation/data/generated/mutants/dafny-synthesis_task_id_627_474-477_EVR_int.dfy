// dafny-synthesis_task_id_627.dfy

method SmallestMissingNumber(s: seq<int>) returns (v: int)
  requires forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] >= 0
  ensures 0 <= v
  ensures v !in s
  ensures forall k: int {:trigger k in s} :: 0 <= k < v ==> k in s
  decreases s
{
  v := 0;
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= v <= i
    invariant v !in s[..i]
    invariant forall k: int {:trigger k in s[..i]} {:trigger s[k]} :: 0 <= k < v && s[k] != v ==> k in s[..i]
  {
    if 0 > v {
      break;
    } else {
      if s[i] == v {
        v := v + 1;
      }
    }
  }
  assert forall k: int {:trigger k in s} {:trigger s[k]} :: 0 <= k < v && s[k] != v ==> k in s;
}
