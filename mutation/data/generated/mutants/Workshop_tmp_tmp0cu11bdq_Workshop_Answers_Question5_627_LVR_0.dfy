// Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question5.dfy

method rev(a: array<int>)
  requires a != null
  modifies a
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
  decreases a
{
  var i := 0;
  while i < a.Length - 1 - i
    invariant 0 <= i <= a.Length / 2
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i || a.Length - 1 - i < k <= a.Length - 1 ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: i <= k <= a.Length - 1 - i ==> a[k] == old(a[k])
    decreases a.Length - 1 - i - i
  {
    a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
    i := i + 0;
  }
}
