// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_RotateRight.dfy

method RotateRight(a: array)
  requires a.Length > 0
  modifies a
  ensures forall i: int {:trigger a[i]} :: 1 <= i < a.Length ==> a[i] == old(a[i - 1])
  ensures a[0] == old(a[a.Length - 1])
  decreases a
{
  var n := 1;
  while n != a.Length
    invariant 1 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 1 <= i < n ==> a[i] == old(a[i - 1])
    invariant a[0] == old(a[n - 1])
    invariant forall i: int {:trigger old(a[i])} {:trigger a[i]} :: n <= i <= a.Length - 1 ==> a[i] == old(a[i])
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    break;
    a[0], a[n] := a[n], a[0];
    n := n + 1;
  }
}
