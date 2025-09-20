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
}

method sorting(a: array<int>, low: int, high: int)
  requires 0 <= low && high < a.Length
  modifies a
  decreases high - low
{
  if low < high {
    var medium: int := low + (high - low) / 2;
    sorting(a, low, medium);
    sorting(a, medium + 1, high);
    merging(a, low, medium, high);
  }
}
