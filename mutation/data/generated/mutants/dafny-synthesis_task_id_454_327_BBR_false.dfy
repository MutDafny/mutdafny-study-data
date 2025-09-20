// dafny-synthesis_task_id_454.dfy

method ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i: int {:trigger s[i]} :: (0 <= i < |s| && s[i] == 'z') || (0 <= i < |s| && s[i] == 'Z')
  decreases s
{
  result := false;
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k: int {:trigger s[k]} :: (0 <= k < i && s[k] == 'z') || (0 <= k < i && s[k] == 'Z')
  {
    if false {
      result := true;
      break;
    }
  }
}
