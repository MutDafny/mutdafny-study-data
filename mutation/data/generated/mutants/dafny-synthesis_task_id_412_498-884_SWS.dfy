// dafny-synthesis_task_id_412.dfy

predicate IsEven(n: int)
  decreases n
{
  n % 2 == 0
}

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
  ensures forall i: int {:trigger evenList[i]} :: (0 <= i < |evenList| ==> IsEven(evenList[i])) && (0 <= i < |evenList| ==> evenList[i] in arr[..])
  ensures forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
  decreases arr
{
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |evenList| <= i
    invariant forall k: int {:trigger evenList[k]} :: (0 <= k < |evenList| ==> IsEven(evenList[k])) && (0 <= k < |evenList| ==> evenList[k] in arr[..])
    invariant forall k: int {:trigger arr[k]} :: 0 <= k < i && IsEven(arr[k]) ==> arr[k] in evenList
  {
    if IsEven(arr[i]) {
      evenList := evenList + [arr[i]];
    }
  }
  evenList := [];
}
