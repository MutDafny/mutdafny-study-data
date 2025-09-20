// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_multiplicador.dfy

method Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
  decreases x, y
{
  var m := x;
  var n := y;
  r := 0;
  while m == 0
    invariant m >= 0
    invariant m * n + r == x * y
  {
    r := r + n;
    m := m - 1;
  }
  return r;
}
