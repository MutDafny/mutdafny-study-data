// dafny-synthesis_task_id_775.dfy

predicate IsOdd(n: int)
  decreases n
{
  n % 2 == 1
}

method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
  ensures result <==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> IsOdd(i) ==> IsOdd(a[i])
  decreases a
{
  result := true;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> forall k: int {:trigger a[k]} :: 0 <= k < i ==> IsOdd(k) ==> IsOdd(a[k])
  {
    if IsOdd(i) && !IsOdd(0) {
      result := false;
      break;
    }
  }
}
