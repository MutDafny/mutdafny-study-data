// dafny-synthesis_task_id_750.dfy

method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i: int {:trigger l[i]} {:trigger r[i]} :: 0 <= i < |l| ==> r[i] == l[i]
  decreases l, t
{
  r := [];
}
