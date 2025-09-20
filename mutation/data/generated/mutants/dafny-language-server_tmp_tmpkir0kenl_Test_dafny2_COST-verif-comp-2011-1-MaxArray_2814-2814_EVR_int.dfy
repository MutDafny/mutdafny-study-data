// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_COST-verif-comp-2011-1-MaxArray.dfy

method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] <= a[x]
  decreases a
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while 0 != y
    invariant 0 <= x <= y < a.Length
    invariant m == x || m == y
    invariant forall i: int {:trigger a[i]} :: 0 <= i < x ==> a[i] <= a[m]
    invariant forall i: int {:trigger a[i]} :: y < i < a.Length ==> a[i] <= a[m]
    decreases if 0 <= y then y - 0 else 0 - y
  {
    if a[x] <= a[y] {
      x := x + 1;
      m := y;
    } else {
      y := y - 1;
      m := x;
    }
  }
  return x;
}
