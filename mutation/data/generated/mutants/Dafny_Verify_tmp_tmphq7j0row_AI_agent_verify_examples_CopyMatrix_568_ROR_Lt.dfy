// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_CopyMatrix.dfy

method CopyMatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i: int, j: int {:trigger old(src[i, j])} {:trigger dst[i, j]} :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
  decreases src, dst
{
  var m := 0;
  while m != src.Length0
    invariant 0 <= m <= src.Length0
    invariant forall i: int, j: int {:trigger old(src[i, j])} {:trigger dst[i, j]} :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
    invariant forall i: int, j: int {:trigger old(src[i, j])} {:trigger src[i, j]} :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i, j] == old(src[i, j])
    decreases if m <= src.Length0 then src.Length0 - m else m - src.Length0
  {
    var n := 0;
    while n < src.Length1
      invariant 0 <= n <= src.Length1
      invariant forall i: int, j: int {:trigger old(src[i, j])} {:trigger dst[i, j]} :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
      invariant forall i: int, j: int {:trigger old(src[i, j])} {:trigger src[i, j]} :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i, j] == old(src[i, j])
      invariant forall j: int {:trigger old(src[m, j])} {:trigger dst[m, j]} :: 0 <= j < n ==> dst[m, j] == old(src[m, j])
      decreases src.Length1 - n
    {
      dst[m, n] := src[m, n];
      n := n + 1;
    }
    m := m + 1;
  }
}
