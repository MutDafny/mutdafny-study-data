// dafny-synthesis_task_id_743.dfy

method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0
  ensures |r| == |l|
  ensures forall i: int {:trigger r[i]} :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
  decreases l, n
{
  var rotated: seq<int> := [];
  for i: int := 1 to |l|
    invariant 0 <= i <= |l|
    invariant |rotated| == i
    invariant forall k: int {:trigger rotated[k]} :: 0 <= k < i ==> rotated[k] == l[(k - n + |l|) % |l|]
  {
    rotated := rotated + [l[(i - n + |l|) % |l|]];
  }
  return rotated;
}
