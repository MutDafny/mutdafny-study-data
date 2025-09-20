// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_DoubleArray.dfy

method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i: int {:trigger old(src[i])} {:trigger dst[i]} :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
  decreases src, dst
{
}
