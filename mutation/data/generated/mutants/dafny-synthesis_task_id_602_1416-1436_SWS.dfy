// dafny-synthesis_task_id_602.dfy

method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k: int, l: int {:trigger s[l], s[k]} :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] != s[j]
  decreases s
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| && !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii: int, jj: int {:trigger s[jj], s[ii]} :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k: int, l: int {:trigger s[l], s[k]} :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii: int, jj: int {:trigger s[jj], s[ii]} :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
    decreases |s| - i
  {
    var j := i + 1;
    found := inner_found;
    while j < |s| && !inner_found
      invariant i < j <= |s|
      invariant inner_found ==> exists k: int {:trigger s[k]} :: i < k < |s| && s[i] == s[k] && s[i] == c
      invariant !inner_found <==> forall k: int {:trigger s[k]} :: i < k < j ==> s[i] != s[k]
      decreases |s| - j
    {
      if s[i] == s[j] {
        inner_found := true;
        c := s[i];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
