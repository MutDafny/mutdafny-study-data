// Metodos_Formais_tmp_tmpbez22nnn_Aula_2_ex2.dfy

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
  var b := x;
  var e := y;
  r := 1;
  while e > 1
    invariant Potencia(b, e) * r == Potencia(x, y)
    decreases e - 1
  {
    r := b * r;
    e := e - 1;
  }
  return r;
}
