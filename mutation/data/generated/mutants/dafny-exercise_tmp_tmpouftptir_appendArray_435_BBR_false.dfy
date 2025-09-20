// dafny-exercise_tmp_tmpouftptir_appendArray.dfy

method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures c.Length == a.Length + b.Length
  ensures forall i: int {:trigger c[i]} {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == c[i]
  ensures forall i: int {:trigger b[i]} :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
  decreases a, b
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger a[j]} {:trigger c[j]} :: 0 <= j < i ==> c[j] == a[j]
    decreases a.Length - i
  {
    c[i] := a[i];
    i := i + 1;
  }
  while false
    invariant a.Length <= i <= b.Length + a.Length
    invariant forall j: int {:trigger c[j]} {:trigger a[j]} :: 0 <= j < a.Length ==> a[j] == c[j]
    invariant forall j: int {:trigger c[j]} :: a.Length <= j < i ==> c[j] == b[j - a.Length]
  {
    c[i] := b[i - a.Length];
    i := i + 1;
  }
}
