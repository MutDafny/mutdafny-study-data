// t1_MF_tmp_tmpi_sqie4j_exemplos_colecoes_arrays_ex5.dfy

method Busca<T(==)>(a: array<T>, x: T) returns (r: int)
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] != x
  decreases a
{
  r := 0;
  while r < a.Length
    invariant 0 <= r <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < r ==> a[i] != x
    decreases a.Length - r
  {
    r := r + 1;
    if a[r] == x {
      return;
    }
  }
  r := -1;
}
