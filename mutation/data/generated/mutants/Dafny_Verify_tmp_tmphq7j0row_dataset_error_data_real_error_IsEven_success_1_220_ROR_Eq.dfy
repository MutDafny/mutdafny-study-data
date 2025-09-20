// Dafny_Verify_tmp_tmphq7j0row_dataset_error_data_real_error_IsEven_success_1.dfy

function even(n: int): bool
  requires n >= 0
  decreases n
{
  if n == 0 then
    true
  else
    !even(n - 1)
}

method is_even(n: int) returns (r: bool)
  requires n >= 0
  ensures r <==> even(n)
  decreases n
{
  var i: int := 0;
  r := true;
  while i == n
    invariant 0 <= i <= n
    invariant r <==> even(i)
  {
    r := !r;
    i := i + 1;
  }
}
