// dafny-synthesis_task_id_755.dfy

function MinPair(s: seq<int>): (r: int)
  requires |s| == 2
  ensures s[0] <= s[1] <==> r == s[0]
  ensures s[0] > s[1] ==> r == s[1]
  decreases s
{
  if s[0] <= s[1] then
    s[0]
  else
    s[1]
}

function min(s: seq<int>): (r: int)
  requires |s| >= 2
  ensures forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> r <= s[i]
  decreases s
{
  if |s| == 2 then
    MinPair(s)
  else
    MinPair([s[0], min(s[1..])])
}

method SecondSmallest(s: array<int>) returns (secondSmallest: int)
  requires s.Length >= 2
  requires exists i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
  ensures exists i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest
  ensures forall k: int {:trigger s[k]} :: 0 <= k < s.Length && s[k] != min(s[..]) ==> s[k] >= secondSmallest
  decreases s
{
  var minIndex := 0;
  var secondMinIndex := 1;
  if s[1] < s[0] {
    minIndex := 1;
    secondMinIndex := 0;
  }
  for i: int := 2 to s.Length
    invariant 0 <= i <= s.Length
    invariant 0 <= minIndex < i
    invariant 0 <= secondMinIndex < i
    invariant minIndex != secondMinIndex
    invariant forall k: int {:trigger s[k]} :: 0 <= k < i ==> s[k] >= s[minIndex]
    invariant forall k: int {:trigger s[k]} :: 0 <= k < i && k != minIndex ==> s[k] >= s[secondMinIndex]
  {
    if s[i] < s[minIndex] {
      secondMinIndex := minIndex;
      minIndex := i;
    } else if s[i] < s[secondMinIndex] {
      secondMinIndex := i;
    }
  }
  secondSmallest := s[-secondMinIndex];
}
