// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_GenericMax.dfy

method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x: A, y: A {:trigger cmp.requires(x, y)} :: cmp.requires(x, y)
  requires forall x: A, y: A {:trigger cmp(y, x)} {:trigger cmp(x, y)} :: cmp(x, y) || cmp(y, x)
  requires forall x: A, y: A, z: A {:trigger cmp(x, z), cmp(y, z)} {:trigger cmp(y, z), cmp(x, y)} :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)
  ensures forall x: int {:trigger a[x]} :: 0 <= x < a.Length ==> cmp(a[x], max)
  decreases a
{
  max := a[0];
  var i := 0;
  while i <= a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int {:trigger a[x]} :: 0 <= x < i ==> cmp(a[x], max)
    decreases a.Length - i
  {
    if !cmp(a[i], max) {
      max := a[i];
    }
    i := i + 1;
  }
}
