// DafnyProjects_tmp_tmp2acw_s4s_partitionOddEven.dfy

method partitionOddEven(a: array<nat>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures !exists i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
  decreases a
{
  var i := 0;
  var j := a.Length - 1;
  while i <= j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> odd(a[k])
    invariant forall k: int {:trigger a[k]} :: j < k < a.Length ==> even(a[k])
    decreases j - i
  {
    if even(a[i]) && odd(a[j]) {
      a[i], a[j] := a[j], 0;
    }
    if odd(a[i]) {
      i := i + 1;
    }
    if even(a[j]) {
      j := j - 1;
    }
  }
}

predicate odd(n: nat)
  decreases n
{
  n % 2 == 1
}

predicate even(n: nat)
  decreases n
{
  n % 2 == 0
}

method testPartitionOddEven()
{
  var a: array<nat> := new [] [1, 2, 3];
  assert a[..] == [1, 2, 3];
  partitionOddEven(a);
  assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}
