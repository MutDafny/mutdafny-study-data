// dafny-synthesis_task_id_431.dfy

method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
  requires a != null && b != null
  ensures result ==> exists i: int, j: int {:trigger b[j], a[i]} :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
  ensures !result ==> forall i: int, j: int {:trigger b[j], a[i]} :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
  decreases a, b
{
  result := false;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant !result ==> forall k: int, j: int {:trigger b[j], a[k]} :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
  {
    for j: int := 0 to b.Length
      invariant 0 <= j <= b.Length
      invariant !result ==> forall k: int {:trigger b[k]} :: 0 <= k < j ==> a[i] != b[k]
    {
      if a[i] <= b[j] {
        result := true;
        return;
      }
    }
  }
}
