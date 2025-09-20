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
  if |s| == 0 {
    result := false;
  } else {
    for i: int := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k: int {:trigger s[k]} :: 0 <= k < i ==> IsDigit(s[k])
    {
      result := false;
      break;
    }
  }
}
