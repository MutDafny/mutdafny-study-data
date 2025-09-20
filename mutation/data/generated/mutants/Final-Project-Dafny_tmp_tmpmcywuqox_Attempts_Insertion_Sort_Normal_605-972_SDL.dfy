// Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Insertion_Sort_Normal.dfy

predicate sorted(a: array<int>)
  reads a
  decreases {a}, a
{
  sortedA(a, a.Length)
}

predicate sortedA(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  reads a
  decreases {a}, a, i
{
  forall k: int, _t#0: int {:trigger a[k], a[_t#0]} | _t#0 == k - 1 :: 
    0 < k &&
    k < i ==>
      a[_t#0] <= a[k]
}

method lookForMin(a: array<int>, i: int) returns (m: int)
  requires 0 <= i < a.Length
  ensures i <= m < a.Length
  ensures forall k: int {:trigger a[k]} :: i <= k < a.Length ==> a[k] >= a[m]
  decreases a, i
{
  var j := i;
  m := i;
  while j < a.Length
    invariant i <= j <= a.Length
    invariant i <= m < a.Length
    invariant forall k: int {:trigger a[k]} :: i <= k < j ==> a[k] >= a[m]
    decreases a.Length - j
  {
    if a[j] < a[m] {
      m := j;
    }
    j := j + 1;
  }
}

method insertionSort(a: array<int>)
  modifies a
  ensures sorted(a)
  decreases a
{
}
