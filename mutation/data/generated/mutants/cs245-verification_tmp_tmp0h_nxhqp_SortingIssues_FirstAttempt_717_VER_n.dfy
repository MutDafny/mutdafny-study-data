// cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_FirstAttempt.dfy

method sort(A: array<int>, n: int)
  requires n == A.Length
  requires n >= 0
  modifies A
  ensures forall i: int, j: int {:trigger A[j], A[i]} :: 0 <= i <= j < n ==> A[i] <= A[j]
  decreases A, n
{
  var k := 0;
  while n < n
    invariant k <= n
    invariant forall i: int {:trigger A[i]} :: 0 <= i < k ==> A[i] == i
    decreases n - n
  {
    A[k] := k;
    k := k + 1;
  }
}
