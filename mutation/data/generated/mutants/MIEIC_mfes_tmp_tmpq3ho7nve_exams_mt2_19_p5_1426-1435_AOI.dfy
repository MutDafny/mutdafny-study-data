// MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p5.dfy

method partition(a: array<T>) returns (pivotPos: int)
  requires a.Length > 0
  modifies a
  ensures 0 <= pivotPos < a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
  ensures forall i: int {:trigger a[i]} :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases a
{
  pivotPos := a.Length - 1;
  var i := 0;
  var j := 0;
  while j < a.Length - 1
    invariant 0 <= i <= j < a.Length
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[k] < a[pivotPos]
    invariant forall k: int {:trigger a[k]} :: i <= k < j ==> a[k] >= a[pivotPos]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases a.Length - 1 - j
  {
    if a[j] < a[pivotPos] {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
    }
    j := j + 1;
  }
  a[a.Length - 1], a[i] := a[i], a[-(a.Length - 1)];
  pivotPos := i;
}

type T = int
