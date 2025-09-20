// dafny-synthesis_task_id_591.dfy

method SwapFirstAndLast(a: array<int>)
  requires a != null && a.Length > 0
  modifies a
  ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
  ensures forall k: int {:trigger old(a[k])} {:trigger a[k]} :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
  decreases a
{
}
