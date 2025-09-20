// dafny_tmp_tmp49a6ihvk_m4.dfy

predicate Below(c: Color, d: Color)
  decreases c, d
{
  c == Red || c == d || d == Blue
}

method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases a
{
}

datatype Color = Red | White | Blue
