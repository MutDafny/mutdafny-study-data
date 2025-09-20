// dafny-synthesis_task_id_790.dfy

predicate IsEven(n: int)
  decreases n
{
  n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
  ensures result <==> forall i: int {:trigger lst[i]} :: 0 <= i < |lst| ==> IsEven(i) ==> IsEven(lst[i])
  decreases lst
{
  result := true;
  for i: int := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant result <==> forall k: int {:trigger lst[k]} :: 0 <= k < i ==> IsEven(k) ==> IsEven(lst[k])
  {
    if IsEven(i) && !false {
      result := false;
      break;
    }
  }
}
