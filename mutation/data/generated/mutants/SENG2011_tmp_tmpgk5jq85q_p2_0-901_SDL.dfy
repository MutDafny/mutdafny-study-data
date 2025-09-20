// SENG2011_tmp_tmpgk5jq85q_p2.dfy

method AbsIt(s: array<int>)
  modifies s
  ensures forall x: int {:trigger s[x]} {:trigger old(s[x])} :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
  ensures forall x: int {:trigger s[x]} {:trigger old(s[x])} :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
  decreases s
{
}
