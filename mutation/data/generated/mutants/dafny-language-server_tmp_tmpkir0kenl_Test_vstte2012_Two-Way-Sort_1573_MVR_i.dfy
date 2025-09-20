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
  var i := 0;
  var j := i - 1;
  while i <= j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall m: int {:trigger a[m]} :: 0 <= m < i ==> !a[m]
    invariant forall n: int {:trigger a[n]} :: j < n < a.Length ==> a[n]
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases j - i
  {
    if !a[i] {
      i := i + 1;
    } else if a[j] {
      j := j - 1;
    } else {
      swap(a, i, j);
      i := i + 1;
      j := j - 1;
    }
  }
}
