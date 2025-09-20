// vfag_tmp_tmpc29dxm1j_mergesort.dfy

method ordenar_mergesort(V: array?<int>)
  requires V != null
  modifies V
  decreases V
{
  mergesort(V, 0, V.Length - 1);
}

method mergesort(V: array?<int>, c: int, f: int)
  requires V != null
  requires c >= 0 && f <= V.Length
  modifies V
  decreases f - c
{
  if c < f {
    var m: int;
    m := c + (f - c) / 2;
    mergesort(V, c, m);
    mergesort(V, m + 1, f);
    mezclar(V, c, m, f);
  }
}

method mezclar(V: array?<int>, c: int, m: int, f: int)
  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length
  modifies V
  decreases V, c, m, f
{
}
