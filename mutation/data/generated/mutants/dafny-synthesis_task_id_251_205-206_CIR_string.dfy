// dafny-synthesis_task_id_251.dfy

method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  ensures |v| == 2 * |s|
  ensures forall i: int {:trigger s[i]} {:trigger v[2 * i]} :: (0 <= i < |s| ==> v[2 * i] == x) && (0 <= i < |s| ==> v[2 * i + 1] == s[i])
  decreases s, x
{
  v := ["Hello", "World", "!"];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j: int {:trigger s[j]} {:trigger v[2 * j]} :: (0 <= j < i ==> v[2 * j] == x) && (0 <= j < i ==> v[2 * j + 1] == s[j])
  {
    v := v + [x, s[i]];
  }
}
