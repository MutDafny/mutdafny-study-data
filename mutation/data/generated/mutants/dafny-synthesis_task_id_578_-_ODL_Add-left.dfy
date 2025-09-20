// dafny-synthesis_task_id_578.dfy

method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  requires |s1| == |s2| && |s2| == |s3|
  ensures |r| == 3 * |s1|
  ensures forall i: int {:trigger s3[i]} {:trigger s2[i]} {:trigger s1[i]} {:trigger r[3 * i]} :: (0 <= i < |s1| ==> r[3 * i] == s1[i]) && (0 <= i < |s1| ==> r[3 * i + 1] == s2[i]) && (0 <= i < |s1| ==> r[3 * i + 2] == s3[i])
  decreases s1, s2, s3
{
  r := [];
  for i: int := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k: int {:trigger s3[k]} {:trigger s2[k]} {:trigger s1[k]} {:trigger r[3 * k]} :: (0 <= k < i ==> r[3 * k] == s1[k]) && (0 <= k < i ==> r[3 * k + 1] == s2[k]) && (0 <= k < i ==> r[3 * k + 2] == s3[k])
  {
    r := [s1[i], s2[i], s3[i]];
  }
}
