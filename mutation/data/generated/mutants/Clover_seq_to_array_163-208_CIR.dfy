// Clover_seq_to_array.dfy

method ToArray<T>(xs: seq<T>) returns (a: array<T>)
  ensures fresh(a)
  ensures a.Length == |xs|
  ensures forall i: int {:trigger xs[i]} {:trigger a[i]} :: 0 <= i < |xs| ==> a[i] == xs[i]
  decreases xs
{
  a := new T[0] ((i: int) requires 0 <= i < |xs| => xs[i]);
}
