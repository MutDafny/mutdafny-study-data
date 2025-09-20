// dafny-synthesis_task_id_396.dfy

method StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
  decreases s
{
  result := s[0] == s[|s| - 2];
}
