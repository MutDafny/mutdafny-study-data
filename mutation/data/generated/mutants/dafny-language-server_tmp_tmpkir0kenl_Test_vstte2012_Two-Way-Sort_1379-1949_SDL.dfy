// dafny-language-server_tmp_tmpkir0kenl_Test_vstte2012_Two-Way-Sort.dfy

method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m: int {:trigger old(a[m])} {:trigger a[m]} :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
  decreases a, i, j
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m: int, n: int {:trigger a[n], a[m]} :: 0 <= m < n < a.Length ==> !a[m] || a[n]
  ensures multiset(a[..]) == old(multiset(a[..]))
  decreases a
{
}
