// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_CopyMatrix.dfy

method CopyMatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i: int, j: int {:trigger old(src[i, j])} {:trigger dst[i, j]} :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
  decreases src, dst
{
}
