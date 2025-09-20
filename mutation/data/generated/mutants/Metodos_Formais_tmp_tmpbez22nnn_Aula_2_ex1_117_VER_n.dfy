// Metodos_Formais_tmp_tmpbez22nnn_Aula_2_ex1.dfy

method Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
  decreases x, y
{
  var m := x;
  var n := y;
  r := 0;
  while n > 0
    invariant m >= 0
    invariant m * n + r == x * y
    decreases n - 0
  {
    r := r + n;
    m := m - 1;
  }
  return r;
}
