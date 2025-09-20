// dafny-synthesis_task_id_436.dfy

predicate IsNegative(n: int)
  decreases n
{
  n < 0
}

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
  ensures forall i: int {:trigger negativeList[i]} :: (0 <= i < |negativeList| ==> IsNegative(negativeList[i])) && (0 <= i < |negativeList| ==> negativeList[i] in arr[..])
  ensures forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
  decreases arr
{
  negativeList := [];
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |negativeList| <= i
    invariant forall k: int {:trigger negativeList[k]} :: (0 <= k < |negativeList| ==> IsNegative(negativeList[k])) && (0 <= k < |negativeList| ==> negativeList[k] in arr[..])
    invariant forall k: int {:trigger arr[k]} :: 0 <= k < i && IsNegative(arr[k]) ==> arr[k] in negativeList
  {
    if IsNegative(-arr[i]) {
      negativeList := negativeList + [arr[i]];
    }
  }
}
