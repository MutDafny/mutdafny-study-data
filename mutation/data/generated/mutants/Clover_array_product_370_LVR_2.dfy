// Clover_array_product.dfy

method arrayProduct(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a.Length == b.Length
  ensures c.Length == a.Length
  ensures forall i: int {:trigger c[i]} {:trigger b[i]} {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] * b[i] == c[i]
  decreases a, b
{
  c := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger c[j]} {:trigger b[j]} {:trigger a[j]} :: 0 <= j < i ==> a[j] * b[j] == c[j]
    decreases a.Length - i
  {
    c[i] := a[i] * b[i];
    i := i + 2;
  }
}
