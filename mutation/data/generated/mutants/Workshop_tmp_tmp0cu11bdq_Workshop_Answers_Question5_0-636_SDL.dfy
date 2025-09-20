// Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question5.dfy

method rev(a: array<int>)
  requires a != null
  modifies a
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
  decreases a
{
}
