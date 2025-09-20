// dafny-synthesis_task_id_760.dfy

method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
  requires a != null
  ensures result ==> forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
  ensures !result ==> exists i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
  decreases a
{
  if a.Length == 0 {
    return true;
  }
  var firstElement := a[0];
  result := true;
  for i: int := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant result ==> forall k: int {:trigger a[k]} :: 0 <= k < i ==> a[k] == firstElement
  {
    if 0 != firstElement {
      result := false;
      break;
    }
  }
}
