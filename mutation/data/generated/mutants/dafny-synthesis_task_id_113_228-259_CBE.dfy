// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
  decreases c
{
  48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> IsDigit(s[i])
  decreases s
{
  result := true;
  result := false;
}
