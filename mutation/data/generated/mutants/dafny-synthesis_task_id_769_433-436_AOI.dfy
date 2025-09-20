// dafny-synthesis_task_id_769.dfy

method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
  ensures forall x: int {:trigger x in b} {:trigger x in a} {:trigger x in diff} :: x in diff <==> x in a && x !in b
  ensures forall i: int, j: int {:trigger diff[j], diff[i]} :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
  decreases a, b
{
  diff := [];
  for i: int := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall x: int {:trigger x in b} {:trigger x in a[..i]} {:trigger x in diff} :: x in diff <==> x in a[..i] && x !in b
    invariant forall i: int, j: int {:trigger diff[j], diff[i]} :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
  {
    if -a[i] !in b && a[i] !in diff {
      diff := diff + [a[i]];
    }
  }
}
