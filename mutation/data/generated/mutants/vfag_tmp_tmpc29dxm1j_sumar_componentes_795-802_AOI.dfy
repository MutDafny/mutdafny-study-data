// vfag_tmp_tmpc29dxm1j_sumar_componentes.dfy

method suma_componentes(V: array?<int>) returns (suma: int)
  requires V != null
  ensures suma == suma_aux(V, 0)
  decreases V
{
  var n: int;
  assert V != null;
  assert 0 <= V.Length <= V.Length && 0 == suma_aux(V, V.Length);
  n := V.Length;
  suma := 0;
  assert 0 <= n <= V.Length && suma == suma_aux(V, n);
  while n != 0
    invariant 0 <= n <= V.Length && suma == suma_aux(V, n)
    decreases n
  {
    assert 0 <= n <= V.Length && suma == suma_aux(V, n) && n != 0;
    assert 0 <= n - 1 <= V.Length;
    assert suma + V[n - 1] == suma_aux(V, n - 1);
    suma := suma + -V[n - 1];
    assert 0 <= n - 1 <= V.Length && suma == suma_aux(V, n - 1);
    n := n - 1;
    assert 0 <= n <= V.Length && suma == suma_aux(V, n);
  }
  assert 0 <= n <= V.Length && suma == suma_aux(V, n) && n == 0;
  assert suma == suma_aux(V, 0);
}

function suma_aux(V: array?<int>, n: int): int
  requires V != null
  requires 0 <= n <= V.Length
  reads V
  decreases V.Length - n
{
  if n == V.Length then
    0
  else
    V[n] + suma_aux(V, n + 1)
}
