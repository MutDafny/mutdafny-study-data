// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_potencia.dfy

function Potencia(x: nat, y: nat): nat
  decreases x, y
{
  if y == 0 then
    1
  else
    x * Potencia(x, y - 1)
}

method Pot(x: nat, y: nat) returns (r: nat)
  ensures r == Potencia(x, y)
  decreases x, y
{
  r := 1;
  var b := x;
  var e := -y;
  while e > 0
    invariant Potencia(b, e) * r == Potencia(x, y)
    decreases e - 0
  {
    r := r * b;
    e := e - 1;
  }
  return r;
}
