// Formal-Methods-Project_tmp_tmphh2ar2xv_BubbleSort.dfy

predicate sorted(a: array?<int>, l: int, u: int)
  requires a != null
  reads a
  decreases {a}, a, l, u
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    0 <= l <= i <= j <= u < a.Length ==>
      a[i] <= a[j]
}

predicate partitioned(a: array?<int>, i: int)
  requires a != null
  reads a
  decreases {a}, a, i
{
  forall k: int, k': int {:trigger a[k'], a[k]} :: 
    0 <= k <= i < k' < a.Length ==>
      a[k] <= a[k']
}

method BubbleSort(a: array?<int>)
  requires a != null
  modifies a
  decreases a
{
  var i := a.Length - 1;
  while false
    invariant sorted(a, i, a.Length - 1)
    invariant partitioned(a, i)
  {
    var j := 0;
    while j < i
      invariant 0 < i < a.Length && 0 <= j <= i
      invariant sorted(a, i, a.Length - 1)
      invariant partitioned(a, i)
      invariant forall k: int {:trigger a[k]} :: 0 <= k <= j ==> a[k] <= a[j]
      decreases i - j
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i - 1;
  }
}

method Main()
{
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
  BubbleSort(a);
  var k := 0;
  while k < 5
    decreases 5 - k
  {
    print a[k], "\n";
    k := k + 1;
  }
}
