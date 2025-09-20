// metodosFormais_tmp_tmp4q2kmya4_T1-MetodosFormais_examples_somatoriov2.dfy

function somaAteAberto(a: array<nat>, i: nat): nat
  requires i <= a.Length
  reads a
  decreases {a}, a, i
{
  if i == 0 then
    0
  else
    a[i - 1] + somaAteAberto(a, i - 1)
}

method somatorio(a: array<nat>) returns (s: nat)
  ensures s == somaAteAberto(a, a.Length)
  decreases a
{
  s := 0;
  for i: int := -1 to a.Length
    invariant s == somaAteAberto(a, i)
  {
    s := s + a[i];
  }
}
