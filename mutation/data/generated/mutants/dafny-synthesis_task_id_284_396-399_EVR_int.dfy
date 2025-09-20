// dafny-synthesis_task_id_284.dfy

method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
  requires a != null
  ensures result ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == n
  ensures !result ==> exists i: int {:trigger a[i]} :: 0 <= i < a.Length && a[i] != n
  decreases a, n
{
  result := true;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result ==> forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[k] == n
  {
    if 0 != n {
      result := false;
      break;
    }
  }
}
