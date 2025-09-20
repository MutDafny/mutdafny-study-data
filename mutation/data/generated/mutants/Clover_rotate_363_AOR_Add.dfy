// Clover_rotate.dfy

method rotate(a: array<int>, offset: int) returns (b: array<int>)
  requires 0 <= offset
  ensures b.Length == a.Length
  ensures forall i: int {:trigger b[i]} :: 0 <= i < a.Length ==> b[i] == a[(i + offset) % a.Length]
  decreases a, offset
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger b[j]} :: 0 <= j < i ==> b[j] == a[(j + offset) % a.Length]
    decreases a.Length - i
  {
    b[i] := a[i + offset + a.Length];
    i := i + 1;
  }
}
