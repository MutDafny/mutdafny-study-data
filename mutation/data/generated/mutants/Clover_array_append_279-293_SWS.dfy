// Clover_array_append.dfy

method append(a: array<int>, b: int) returns (c: array<int>)
  ensures a[..] + [b] == c[..]
  decreases a, b
{
  c := new int[a.Length + 1];
  var i := 0;
  c[a.Length] := b;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall ii: int {:trigger a[ii]} {:trigger c[ii]} :: 0 <= ii < i ==> c[ii] == a[ii]
    decreases a.Length - i
  {
    c[i] := a[i];
    i := i + 1;
  }
}
