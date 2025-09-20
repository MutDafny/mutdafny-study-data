// Metodos_Formais_tmp_tmpbez22nnn_Aula_4_ex3.dfy

function Fib(n: nat): nat
  decreases n
{
  if n < 2 then
    n
  else
    Fib(n - 2) + Fib(n - 1)
}

method ComputeFib(n: nat) returns (x: nat)
  ensures x == Fib(n)
  decreases n
{
  var i := 0;
  x := 0;
  var y := 1;
  while i < n
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i + 1)
    decreases n - i
  {
    x, y := y, x + y;
    i := i + 1;
  }
}

method Teste()
{
  var n := 3;
  var f := ComputeFib(-n);
  assert f == 2;
}
