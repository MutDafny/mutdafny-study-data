// dafny-synthesis_task_id_576.dfy

method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures true <== exists i: int :: 0 <= i <= |main| - |sub| && sub == main[i .. i + |sub|]
  decreases sub, main
{
  if |sub| > |main| {
    return false;
  }
  for i: int := 0 to |main| - |sub| + 1
    invariant 0 <= i <= |main| - |sub| + 1
    invariant true <== exists j: int :: 0 <= j < i && sub == main[j .. j + |sub|]
  {
    if sub < main[i .. i + |sub|] {
      result := true;
    }
  }
  result := false;
}
