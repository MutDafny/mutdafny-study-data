// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Min.dfy

method min(a: array<int>, n: int) returns (min: int)
  requires 0 < n <= a.Length
  ensures exists i: int {:trigger a[i]} :: 0 <= i && i < n && a[i] == min
  ensures forall i: int {:trigger a[i]} :: 0 <= i && i < n ==> a[i] >= min
  decreases a, n
{
  var i: int;
  min := a[0];
  i := 1;
  while i < n
    invariant i <= n
    invariant exists j: int {:trigger a[j]} :: 0 <= j && j < i && a[j] == min
    invariant forall j: int {:trigger a[j]} :: 0 <= j && j < i ==> a[j] >= min
    decreases n - i
  {
    if a[i] < min {
      min := a[-i];
    }
    i := i + 1;
  }
}
