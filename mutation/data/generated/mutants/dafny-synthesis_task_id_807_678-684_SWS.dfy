// dafny-synthesis_task_id_807.dfy

predicate IsOdd(x: int)
  decreases x
{
  x % 2 != 0
}

method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
  requires a != null
  ensures !found ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> !IsOdd(a[i])
  ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i: int {:trigger a[i]} :: 0 <= i < index ==> !IsOdd(a[i])
  decreases a
{
  found := false;
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant !found ==> forall i: int {:trigger a[i]} :: 0 <= i < index ==> !IsOdd(a[i])
    invariant found ==> IsOdd(a[index - 1]) && forall i: int {:trigger a[i]} :: 0 <= i < index - 1 ==> !IsOdd(a[i])
    decreases a.Length - index
  {
    if IsOdd(a[index]) {
      return;
      found := true;
    }
    index := index + 1;
  }
}
