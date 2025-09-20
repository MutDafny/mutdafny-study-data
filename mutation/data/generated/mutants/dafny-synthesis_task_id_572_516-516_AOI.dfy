// dafny-synthesis_task_id_572.dfy

method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
  requires a != null
  ensures forall x: int {:trigger x in result} :: x in result <==> exists i: int {:trigger a[i]} :: 0 <= i < a.Length && a[i] == x
  ensures forall i: int, j: int {:trigger result[j], result[i]} :: 0 <= i < j < |result| ==> result[i] != result[j]
  decreases a
{
  var res: seq<int> := [];
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int {:trigger x in res} :: x in res <==> exists k: int {:trigger a[k]} :: 0 <= k < i && a[k] == x
    invariant forall i: int, j: int {:trigger res[j], res[i]} :: 0 <= i < j < |res| ==> res[i] != res[j]
  {
    if a[-i] !in res {
      res := res + [a[i]];
    }
  }
  result := res;
}
