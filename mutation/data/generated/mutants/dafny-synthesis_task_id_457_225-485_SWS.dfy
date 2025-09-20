// dafny-synthesis_task_id_457.dfy

method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
  requires |s| > 0
  ensures minSublist in s
  ensures forall sublist: seq<int> {:trigger |sublist|} {:trigger sublist in s} :: sublist in s ==> |minSublist| <= |sublist|
  decreases s
{
  for i: int := 1 to |s|
    invariant 0 <= i <= |s|
    invariant minSublist in s[..i]
    invariant forall sublist: seq<int> {:trigger |sublist|} {:trigger sublist in s[..i]} :: sublist in s[..i] ==> |minSublist| <= |sublist|
  {
    if |s[i]| < |minSublist| {
      minSublist := s[i];
    }
  }
  minSublist := s[0];
}
