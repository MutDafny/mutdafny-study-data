// dafny-duck_tmp_tmplawbgxjo_p3.dfy

method max(x: array<nat>) returns (y: nat)
  requires x.Length > 0
  ensures forall j: int {:trigger x[j]} :: 0 <= j < x.Length ==> y >= x[j]
  ensures y in x[..]
  decreases x
{
  y := x[0];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall j: int {:trigger x[j]} :: 0 <= j < i ==> y >= x[j]
    invariant y in x[..]
    decreases x.Length - i
  {
    if y <= x[i] {
      y := x[i];
    }
  }
  assert y in x[..];
}

method Main()
{
  var a := new nat[6] [5, 1, 3, 6, 12, 3];
  var c := max(a);
  assert c == 12;
}
