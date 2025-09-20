// dafny-synthesis_task_id_426.dfy

predicate IsOdd(n: int)
  decreases n
{
  n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures forall i: int {:trigger oddList[i]} :: (0 <= i < |oddList| ==> IsOdd(oddList[i])) && (0 <= i < |oddList| ==> oddList[i] in arr[..])
  ensures forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
  decreases arr
{
  oddList := [];
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |oddList| <= i
    invariant forall k: int {:trigger oddList[k]} :: (0 <= k < |oddList| ==> IsOdd(oddList[k])) && (0 <= k < |oddList| ==> oddList[k] in arr[..])
    invariant forall k: int {:trigger arr[k]} :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
  {
    oddList := oddList + [arr[i]];
  }
}
