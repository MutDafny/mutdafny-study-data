// dafny-synthesis_task_id_808.dfy

method ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
  decreases s, k
{
  result := false;
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j: int {:trigger s[j]} :: 0 <= j < i && s[j] == k
  {
    if s[i] <= k {
      result := true;
      break;
    }
  }
}
