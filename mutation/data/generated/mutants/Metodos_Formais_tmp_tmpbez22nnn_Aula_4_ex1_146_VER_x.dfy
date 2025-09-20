// Metodos_Formais_tmp_tmpbez22nnn_Aula_4_ex1.dfy

predicate Par(n: int)
  decreases n
{
  n % 2 == 0
}

method FazAlgo(a: int, b: int)
    returns (x: int, y: int)
  requires a >= b && Par(a - b)
  decreases a, b
{
  x := a;
  y := x;
  while x != y
    invariant x >= y
    invariant Par(x - y)
    decreases x - y
  {
    x := x - 1;
    y := y + 1;
  }
}
