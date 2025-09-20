// Dafny-programs_tmp_tmpnso9eu7u_Algorithms + sorting_bubble-sort.dfy

predicate sorted_between(A: array<int>, from: int, to: int)
  reads A
  decreases {A}, A, from, to
{
  forall i: int, j: int {:trigger A[j], A[i]} :: 
    0 <= i <= j < A.Length &&
    from <= i <= j <= to ==>
      A[i] == A[j]
}

predicate sorted(A: array<int>)
  reads A
  decreases {A}, A
{
  sorted_between(A, 0, A.Length - 1)
}

method BubbleSort(A: array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
  decreases A
{
  var N := A.Length;
  var i := N - 1;
  while 0 < i
    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant sorted_between(A, i, N - 1)
    invariant forall n: int, m: int {:trigger A[m], A[n]} :: 0 <= n <= i < m < N ==> A[n] <= A[m]
    decreases i
  {
    print A[..], "\n";
    var j := 0;
    while j < i
      invariant 0 < i < N
      invariant 0 <= j <= i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, i, N - 1)
      invariant forall n: int, m: int {:trigger A[m], A[n]} :: 0 <= n <= i < m < N ==> A[n] <= A[m]
      invariant forall n: int {:trigger A[n]} :: 0 <= n <= j ==> A[n] <= A[j]
      decreases i - j
    {
      if A[j] > A[j + 1] {
        A[j], A[j + 1] := A[j + 1], A[j];
        print A[..], "\n";
      }
      j := j + 1;
    }
    i := i - 1;
    print "\n";
  }
}

method Main()
{
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  BubbleSort(A);
  print A[..];
}
