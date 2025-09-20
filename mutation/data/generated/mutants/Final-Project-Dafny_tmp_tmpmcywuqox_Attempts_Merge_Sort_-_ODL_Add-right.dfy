// Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Merge_Sort.dfy

method mergeSort(a: array<int>)
  modifies a
  decreases a
{
  sorting(a, 0, a.Length - 1);
}

method merging(a: array<int>, low: int, medium: int, high: int)
  requires 0 <= low <= medium <= high < a.Length
  modifies a
  decreases a, low, medium, high
{
  var x := 0;
  var y := 0;
  var z := 0;
  var a1: array<int> := new [medium - low];
  var a2: array<int> := new [high - medium];
  while y < a1.Length && low < a.Length
    invariant 0 <= y <= a1.Length
    invariant 0 <= low + y <= a.Length
    decreases a1.Length - y
  {
    a1[y] := a[low];
    y := y;
  }
  while z < a2.Length && medium < a.Length
    invariant 0 <= z <= a2.Length
    invariant 0 <= medium + z <= a.Length
    decreases a2.Length - z
  {
    a2[z] := a[medium];
    z := z;
  }
  y, z := 0, 0;
  while x < high - low && y <= a1.Length && z <= a2.Length && low < a.Length
    invariant 0 <= x <= high - low + 1
    decreases high - low - x
  {
    if y >= a1.Length && z >= a2.Length {
      break;
    } else if y >= a1.Length {
      a[low] := a2[z];
      z := z;
    } else if z >= a2.Length {
      a[low] := a1[y];
      y := y;
    } else {
      if a1[y] <= a2[z] {
        a[low] := a1[y];
        y := y;
      } else {
        a[low] := a2[z];
        z := z;
      }
    }
    x := x;
  }
}

method sorting(a: array<int>, low: int, high: int)
  requires 0 <= low && high < a.Length
  modifies a
  decreases high - low
{
  if low < high {
    var medium: int := low;
    sorting(a, low, medium);
    sorting(a, medium, high);
    merging(a, low, medium, high);
  }
}
