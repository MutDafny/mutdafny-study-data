// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
  decreases c
{
  48 <= c as int <= 57
}

method CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int {:trigger s[i]} | 0 <= i < |s| && IsDigit(s[i])|
  decreases s
{
  var digits := set i: int {:trigger s[i]} | 0 <= i < |s| && IsDigit(s[i]);
  count := 0;
}
