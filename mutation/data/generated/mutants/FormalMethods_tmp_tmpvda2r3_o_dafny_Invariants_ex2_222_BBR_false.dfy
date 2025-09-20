// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex2.dfy

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
  var e := y;
  while false
    invariant Potencia(b, e) * r == Potencia(x, y)
  {
    r := r * b;
    e := e - 1;
  }
  return r;
}
