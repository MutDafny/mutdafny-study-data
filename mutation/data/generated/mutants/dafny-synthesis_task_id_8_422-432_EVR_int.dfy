// dafny-synthesis_task_id_8.dfy

method SquareElements(a: array<int>) returns (squared: array<int>)
  ensures squared.Length == a.Length
  ensures forall i: int {:trigger a[i]} {:trigger squared[i]} :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
  decreases a
{
  squared := new int[a.Length];
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant squared.Length == a.Length
    invariant forall k: int {:trigger a[k]} {:trigger squared[k]} :: 0 <= k < i ==> squared[k] == a[k] * a[k]
  {
    squared[i] := 0;
  }
}
