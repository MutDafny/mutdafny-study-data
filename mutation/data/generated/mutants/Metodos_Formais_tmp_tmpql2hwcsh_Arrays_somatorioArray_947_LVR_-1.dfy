// Metodos_Formais_tmp_tmpql2hwcsh_Arrays_somatorioArray.dfy

function soma(a: array<nat>, i: nat): nat
  requires i <= a.Length
  reads a
  decreases {a}, a, i
{
  if i == 0 then
    0
  else
    a[i - 1] + soma(a, i - 1)
}

method somatorio(a: array<nat>) returns (s: nat)
  ensures s == soma(a, a.Length)
  decreases a
{
  s := 0;
  for i: int := -1 to a.Length
    invariant s == soma(a, i)
  {
    s := s + a[i];
  }
}
