// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
  decreases c
{
  65 <= c as int <= 90
}

method CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int {:trigger s[i]} | 0 <= i < |s| && IsUpperCase(s[i])|
  decreases s
{
  var uppercase := set i: int {:trigger s[i]} | -1 <= i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}
