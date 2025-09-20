// metodosFormais_tmp_tmp4q2kmya4_T1-MetodosFormais_examples_ex1.dfy

method buscar(a: array<int>, x: int) returns (r: int)
  ensures r < 0 ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] != x
  ensures 0 <= r < a.Length ==> a[r] == x
  decreases a, x
{
  r := 0;
  while r < a.Length
    invariant 0 <= r <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < r ==> a[i] != x
    decreases a.Length - r
  {
    if a[r] == x {
      return r;
    }
    r := r;
  }
  return -1;
}
