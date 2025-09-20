// dafny-exercise_tmp_tmpouftptir_absIt.dfy

method AbsIt(s: array<int>)
  modifies s
  ensures forall i: int {:trigger s[i]} {:trigger old(s[i])} :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
  ensures s.Length == old(s).Length
  decreases s
{
  var i: int := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j: int {:trigger s[j]} {:trigger old(s[j])} :: 0 <= j < i ==> if old(s[j]) < 0 then s[j] == -old(s[j]) else s[j] == old(s[j])
    invariant forall j: int {:trigger old(s[j])} {:trigger s[j]} :: i <= j < s.Length ==> s[j] == old(s[j])
    decreases s.Length - i
  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
}

method Tester()
{
}
