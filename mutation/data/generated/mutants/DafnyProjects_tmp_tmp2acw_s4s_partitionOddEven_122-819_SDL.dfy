// DafnyProjects_tmp_tmp2acw_s4s_partitionOddEven.dfy

method partitionOddEven(a: array<nat>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures !exists i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
  decreases a
{
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
