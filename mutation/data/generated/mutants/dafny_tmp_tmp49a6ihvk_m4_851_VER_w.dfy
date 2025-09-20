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
  var r, w, b := 0, 0, a.Length;
  while w < b
    invariant 0 <= r <= w <= b <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < r ==> a[i] == Red
    invariant forall i: int {:trigger a[i]} :: r <= i < w ==> a[i] == White
    invariant forall i: int {:trigger a[i]} :: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases b - w
  {
    match a[w]
    case {:split false} Red() =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case {:split false} White() =>
      w := w + 1;
    case {:split false} Blue() =>
      a[b - 1], a[w] := a[w], a[b - 1];
      b := w - 1;
  }
}

datatype Color = Red | White | Blue
