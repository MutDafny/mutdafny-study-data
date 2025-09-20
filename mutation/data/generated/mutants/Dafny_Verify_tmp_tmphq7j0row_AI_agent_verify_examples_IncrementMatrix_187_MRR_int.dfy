// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_IncrementMatrix.dfy

method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
  decreases a
{
  var m := 0;
  while m != 0
    invariant 0 <= m <= a.Length0
    invariant forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
    invariant forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
    decreases if m <= 0 then 0 - m else m - 0
  {
    var n := 0;
    while n != a.Length1
      invariant 0 <= n <= a.Length1
      invariant forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
      invariant forall i: int, j: int {:trigger old(a[i, j])} {:trigger a[i, j]} :: m < i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
      invariant forall j: int {:trigger old(a[m, j])} {:trigger a[m, j]} :: 0 <= j < n ==> a[m, j] == old(a[m, j]) + 1
      invariant forall j: int {:trigger old(a[m, j])} {:trigger a[m, j]} :: n <= j < a.Length1 ==> a[m, j] == old(a[m, j])
      decreases if n <= a.Length1 then a.Length1 - n else n - a.Length1
    {
      a[m, n] := a[m, n] + 1;
      n := n + 1;
    }
    m := m + 1;
  }
}
