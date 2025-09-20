// cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode.dfy

method BubbleSort(A: array<int>, n: int)
  requires A.Length >= 0 && n == A.Length
  modifies A
  decreases A, n
{
}
