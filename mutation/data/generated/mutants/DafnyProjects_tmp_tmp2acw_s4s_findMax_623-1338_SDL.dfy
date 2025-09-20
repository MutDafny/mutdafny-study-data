// DafnyProjects_tmp_tmp2acw_s4s_findMax.dfy

method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k: int {:trigger a[k]} :: 0 <= k < a.Length && max == a[k]
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> max >= a[k]
  decreases a
{
  max := a[0];
  for i: int := 1 to a.Length
    invariant exists k: int {:trigger a[k]} :: 0 <= k < i && max == a[k]
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> max >= a[k]
  {
    if a[i] > max {
      max := a[i];
    }
  }
}

method testFindMax()
{
}
