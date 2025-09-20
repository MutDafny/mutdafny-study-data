// SENG2011_tmp_tmpgk5jq85q_p2.dfy

method AbsIt(s: array<int>)
  modifies s
  ensures forall x: int {:trigger s[x]} {:trigger old(s[x])} :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
  ensures forall x: int {:trigger s[x]} {:trigger old(s[x])} :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
  decreases s
{
  var i: int := 0;
  while true
    invariant 0 <= i <= s.Length
    invariant forall k: int {:trigger s[k]} {:trigger old(s[k])} :: 0 <= k < i ==> old(s[k]) < 0 ==> s[k] == -old(s[k])
    invariant forall k: int {:trigger s[k]} {:trigger old(s[k])} :: 0 <= k < i ==> old(s[k]) >= 0 ==> s[k] == old(s[k])
    invariant forall k: int {:trigger s[k]} {:trigger old(s[k])} :: i <= k < s.Length ==> old(s[k]) == s[k]
  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
}
