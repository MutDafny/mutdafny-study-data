// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy

method square(n: int) returns (r: int)
  requires 0 <= n
  ensures r == n * n
  decreases n
{
  var x: int;
  var i: int;
  r := 0;
  i := 0;
  while i < n
    invariant i <= n
    invariant r == i * i
    invariant x == 2 * i + 1
    decreases n - i
  {
    r := r + x;
    x := x + 2;
    i := i + 1;
  }
  x := 1;
}
