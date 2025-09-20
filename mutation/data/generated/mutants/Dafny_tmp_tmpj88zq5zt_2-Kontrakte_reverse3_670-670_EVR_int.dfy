// Dafny_tmp_tmpj88zq5zt_2-Kontrakte_reverse3.dfy

method swap3(a: array<int>, h: int, i: int, j: int)
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  modifies a
  ensures a[h] == old(a[i])
  ensures a[j] == old(a[h])
  ensures a[i] == old(a[j])
  ensures forall k: int {:trigger old(a[k])} {:trigger a[k]} :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k])
  decreases a, h, i, j
{
  var tmp := a[h];
  a[h] := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

method testSwap3(a: array<int>, h: int, i: int, j: int)
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  modifies a
  decreases a, h, i, j
{
  swap3(a, h, i, 0);
  assert a[h] == old(a[i]);
  assert a[j] == old(a[h]);
  assert a[i] == old(a[j]);
  assert forall k: int {:trigger old(a[k])} {:trigger a[k]} :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]);
}
