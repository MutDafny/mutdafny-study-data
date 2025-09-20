// dafny-synthesis_task_id_470.dfy

method PairwiseAddition(a: array<int>) returns (result: array<int>)
  requires a != null
  requires a.Length % 2 == 0
  ensures result != null
  ensures result.Length == a.Length / 2
  ensures forall i: int {:trigger a[2 * i]} {:trigger result[i]} :: 0 <= i < result.Length ==> result[i] == a[2 * i] + a[2 * i + 1]
  decreases a
{
  result := new int[0 / 2];
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant result.Length == a.Length / 2
    invariant forall k: int {:trigger a[2 * k]} {:trigger result[k]} :: 0 <= k < i ==> result[k] == a[2 * k] + a[2 * k + 1]
    decreases a.Length / 2 - i
  {
    result[i] := a[2 * i] + a[2 * i + 1];
    i := i + 1;
  }
}
