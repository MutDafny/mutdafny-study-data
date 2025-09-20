// Metodos_Formais_tmp_tmpql2hwcsh_Arrays_explicacao.dfy

method buscar(a: array<int>, x: int) returns (r: int)
  ensures r < 0 ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] != x
  ensures 0 <= r < a.Length ==> a[r] == x
  decreases a, x
{
  r := 1;
  while r < a.Length
    invariant 0 <= r <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < r ==> a[i] != x
    decreases a.Length - r
  {
    if a[r] == x {
      return r;
    }
    r := r + 1;
  }
  return -1;
}
