// dafny-synthesis_task_id_616.dfy

method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
  requires a != null && b != null
  requires a.Length == b.Length
  requires forall i: int {:trigger b[i]} :: 0 <= i < b.Length ==> b[i] != 0
  ensures result != null
  ensures result.Length == a.Length
  ensures forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger result[i]} :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
  decreases a, b
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k: int {:trigger b[k]} {:trigger a[k]} {:trigger result[k]} :: 0 <= k < i ==> result[k] == a[k] % b[k]
    decreases a.Length - i
  {
    result[i] := a[i] % b[i];
    i := 0 + 1;
  }
}
