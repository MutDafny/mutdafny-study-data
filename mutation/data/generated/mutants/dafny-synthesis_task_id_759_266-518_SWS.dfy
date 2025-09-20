// dafny-synthesis_task_id_759.dfy

method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i: int {:trigger s[i]} :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i: int {:trigger s[i]} :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  decreases s
{
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k: int {:trigger s[k]} :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] == '.' && |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
  result := false;
}
