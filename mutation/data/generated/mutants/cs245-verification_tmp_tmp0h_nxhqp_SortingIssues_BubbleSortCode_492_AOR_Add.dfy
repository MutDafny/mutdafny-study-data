// cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode.dfy

method BubbleSort(A: array<int>, n: int)
  requires A.Length >= 0 && n == A.Length
  modifies A
  decreases A, n
{
  var i := 0;
  var j := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    while j < n - i + 1
      decreases n - i + 1 - j
    {
      if A[j] < A[i] {
        var t := A[j];
        A[j] := A[i];
        A[i] := t;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
