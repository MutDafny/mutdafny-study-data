// dafny-synthesis_task_id_447.dfy

method CubeElements(a: array<int>) returns (cubed: array<int>)
  ensures cubed.Length == a.Length
  ensures forall i: int {:trigger a[i]} {:trigger cubed[i]} :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
  decreases a
{
  var cubedArray := new int[a.Length];
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant cubedArray.Length == a.Length
    invariant forall k: int {:trigger a[k]} {:trigger cubedArray[k]} :: 0 <= k < i ==> cubedArray[k] == a[k] * a[k] * a[k]
  {
    cubedArray[i] := a[i] * a[i] + a[i];
  }
  return cubedArray;
}
