// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_IncrementMatrix.dfy

method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
  decreases a
{
}
