// DafnyPrograms_tmp_tmp74_f9k_c_invertarray.dfy

method InvertArray(a: array<int>)
  modifies a
  ensures forall i: int {:trigger a[i]} | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
  decreases a
{
  var index := 0;
  while index < a.Length / 2
    invariant 0 <= index <= a.Length / 2
    invariant forall i: int {:trigger a[i]} | 0 <= i < index :: a[i] == old(a[a.Length - 1 - i])
    invariant forall i: int {:trigger old(a[i])} | 0 <= i < index :: a[a.Length - 1 - i] == old(a[i])
    invariant forall i: int {:trigger old(a[i])} {:trigger a[i]} | index <= i < a.Length - index :: a[i] == old(a[i])
    decreases a.Length / 2 - index
  {
    a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
    index := 1;
  }
}
