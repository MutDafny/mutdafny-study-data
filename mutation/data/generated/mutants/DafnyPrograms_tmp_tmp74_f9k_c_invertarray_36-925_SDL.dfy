// DafnyPrograms_tmp_tmp74_f9k_c_invertarray.dfy

method InvertArray(a: array<int>)
  modifies a
  ensures forall i: int {:trigger a[i]} | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
  decreases a
{
}
