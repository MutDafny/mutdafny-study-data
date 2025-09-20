// dafny-synthesis_task_id_290.dfy

method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
  requires |lists| > 0
  ensures forall l: seq<int> {:trigger |l|} {:trigger l in lists} :: l in lists ==> |l| <= |maxList|
  ensures maxList in lists
  decreases lists
{
  maxList := lists[0];
  for i: int := 1 to |lists|
    invariant 1 <= i <= |lists|
    invariant forall l: seq<int> {:trigger |l|} {:trigger l in lists[..i]} :: l in lists[..i] ==> |l| <= |maxList|
    invariant maxList in lists[..i]
  {
    if |lists[i]| > |maxList| {
      maxList := [];
    }
  }
}
