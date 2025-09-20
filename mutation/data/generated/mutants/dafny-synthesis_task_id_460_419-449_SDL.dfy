// dafny-synthesis_task_id_460.dfy

method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
  requires forall i: int {:trigger lst[i]} :: 0 <= i < |lst| ==> |lst[i]| > 0
  ensures |result| == |lst|
  ensures forall i: int {:trigger lst[i]} {:trigger result[i]} :: 0 <= i < |result| ==> result[i] == lst[i][0]
  decreases lst
{
  result := [];
  for i: int := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant |result| == i
    invariant forall j: int {:trigger lst[j]} {:trigger result[j]} :: 0 <= j < i ==> result[j] == lst[j][0]
  {
  }
}
