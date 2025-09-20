// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ArrayMap.dfy

method ArrayMap<A>(f: int -> A, a: array<A>)
  requires a != null
  requires forall j: int {:trigger f.requires(j)} :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j: int {:trigger f.reads(j)} :: 0 <= j < a.Length ==> a !in f.reads(j)
  modifies a
  ensures forall j: int {:trigger f(j)} {:trigger a[j]} :: 0 <= j < a.Length ==> a[j] == f(j)
  decreases a
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger f(j)} {:trigger a[j]} :: 0 <= j < i ==> a[j] == f(j)
    decreases a.Length - i
  {
    a[i] := f(i);
    i := i;
  }
}
