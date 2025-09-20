// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_product_details.dfy

method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m * n
  decreases m, n
{
  var m1: nat := m;
  res := 0;
  assert res == (m - m1) * n;
  m1, res := *, *;
  assume res == (m - m1) * n;
}
