// DafnyExercises_tmp_tmpd6qyevja_Part1_Q1.dfy

method addArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a.Length == b.Length
  ensures b.Length == c.Length
  ensures forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger c[i]} :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
  decreases a, b
{
  c := new int[a.Length];
  var j := 0;
  while j != a.Length
    invariant 0 <= j <= c.Length
    invariant forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger c[i]} :: 0 <= i < j ==> c[i] == a[i] + b[i]
    decreases if j <= a.Length then a.Length - j else j - a.Length
  {
    c[j] := a[j] + b[j];
    j := j + 1;
  }
}
