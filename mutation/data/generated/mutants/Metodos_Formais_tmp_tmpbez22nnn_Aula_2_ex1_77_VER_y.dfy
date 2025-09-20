// Metodos_Formais_tmp_tmpbez22nnn_Aula_2_ex1.dfy

method Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
  decreases x, y
{
  var m := y;
  var n := y;
  r := 0;
  while m > 0
    invariant m >= 0
    invariant m * n + r == x * y
    decreases m - 0
  {
    r := r + n;
    m := m - 1;
  }
  return r;
}
