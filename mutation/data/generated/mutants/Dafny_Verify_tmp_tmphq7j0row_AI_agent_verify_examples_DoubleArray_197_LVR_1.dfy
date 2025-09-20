// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_DoubleArray.dfy

method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i: int {:trigger old(src[i])} {:trigger dst[i]} :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
  decreases src, dst
{
  var n := 1;
  while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i: int {:trigger old(src[i])} {:trigger dst[i]} :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    invariant forall i: int {:trigger old(src[i])} {:trigger src[i]} :: n <= i < src.Length ==> src[i] == old(src[i])
    decreases if n <= src.Length then src.Length - n else n - src.Length
  {
    dst[n] := 2 * src[n];
    n := n + 1;
  }
}
