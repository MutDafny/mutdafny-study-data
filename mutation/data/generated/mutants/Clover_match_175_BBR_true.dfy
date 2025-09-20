// Clover_match.dfy

method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n: int {:trigger p[n]} {:trigger s[n]} :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
  decreases s, p
{
  var i := 0;
  while true
    invariant 0 <= i <= |s|
    invariant forall n: int {:trigger p[n]} {:trigger s[n]} :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}
