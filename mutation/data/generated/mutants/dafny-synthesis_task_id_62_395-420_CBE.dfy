// dafny-synthesis_task_id_62.dfy

method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i: int {:trigger s[i]} :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i: int {:trigger s[i]} :: 0 <= i < s.Length && min == s[i]
  decreases s
{
  min := s[0];
  for i: int := 1 to s.Length
    invariant 0 <= i <= s.Length
    invariant forall k: int {:trigger s[k]} :: 0 <= k < i ==> min <= s[k]
    invariant exists k: int {:trigger s[k]} :: 0 <= k < i && min == s[k]
  {
    min := s[i];
  }
}
