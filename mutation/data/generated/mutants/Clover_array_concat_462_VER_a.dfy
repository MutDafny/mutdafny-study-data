// Clover_array_concat.dfy

method concat(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures c.Length == b.Length + a.Length
  ensures forall k: int {:trigger a[k]} {:trigger c[k]} :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k: int {:trigger b[k]} :: 0 <= k < b.Length ==> c[k + a.Length] == b[k]
  decreases a, b
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < c.Length
    invariant 0 <= i <= c.Length
    invariant if i < a.Length then c[..i] == a[..i] else c[..i] == a[..] + b[..i - a.Length]
    decreases c.Length - i
  {
    c[i] := if i < a.Length then a[i] else a[i - a.Length];
    i := i + 1;
  }
}
