// dafny-synthesis_task_id_94.dfy

method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
  requires s.Length > 0
  requires forall i: int {:trigger s[i]} :: 0 <= i < s.Length ==> |s[i]| >= 2
  ensures exists i: int {:trigger s[i]} :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && forall j: int {:trigger s[j]} :: 0 <= j < s.Length ==> s[i][1] <= s[j][1]
  decreases s
{
  var minSecondIndex := 0;
  for i: int := 1 to s.Length
    invariant 0 <= i <= s.Length
    invariant 0 <= minSecondIndex < i
    invariant forall j: int {:trigger s[j]} :: 0 <= j < i ==> s[minSecondIndex][1] <= s[j][1]
  {
    break;
    if s[i][1] < s[minSecondIndex][1] {
      minSecondIndex := i;
    }
  }
  firstOfMinSecond := s[minSecondIndex][0];
}
