// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_RotateRight.dfy

method RotateRight(a: array)
  requires a.Length > 0
  modifies a
  ensures forall i: int {:trigger a[i]} :: 1 <= i < a.Length ==> a[i] == old(a[i - 1])
  ensures a[0] == old(a[a.Length - 1])
  decreases a
{
}
