// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_SmallNum.dfy

method add_small_numbers(a: array<int>, n: int, max: int)
    returns (r: int)
  requires n > 0
  requires n <= a.Length
  requires forall i: int {:trigger a[i]} :: 0 <= i && i < n ==> a[i] <= max
  ensures r <= max * n
  decreases a, n, max
{
  var i: int;
  r := 0;
  i := 0;
  while i < n
    invariant i <= n
    invariant r <= max * i
    decreases n - i
  {
    r := r + a[i];
    i := i + 1;
  }
}
