// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_Classics.dfy

ghost function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n)
  decreases n
{
  u := 1;
  var r := 0;
  while r < n
    invariant 0 <= r <= n
    invariant u == Factorial(r)
    decreases n - r
  {
    var v := u;
    var s := 1;
    while s <= r
      invariant 1 <= s <= r + 1
      invariant u == s * Factorial(r)
      decreases r - s
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N
  requires 0 <= f < N
  modifies A
  ensures forall p: int, q: int {:trigger A[q], A[p]} :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
  decreases A, N, f
{
  var m, n := 0, N - 1;
  while m < n
    invariant 0 <= m <= f <= n < N
    invariant forall p: int, q: int {:trigger A[q], A[p]} :: 0 <= p < m <= q < N ==> A[p] <= A[q]
    invariant forall p: int, q: int {:trigger A[q], A[p]} :: 0 <= p <= n < q < N ==> A[p] <= A[q]
    decreases n - m
  {
    var r, i, j := A[f], m, n;
    while i <= j
      invariant m <= i && j <= n
      invariant -1 <= j && i <= N
      invariant i <= j ==> exists g: int {:trigger A[g]} :: i <= g < N && r <= A[g]
      invariant i <= j ==> exists g: int {:trigger A[g]} :: 0 <= g <= j && A[g] <= r
      invariant forall p: int {:trigger A[p]} :: 0 <= p < i ==> A[p] <= r
      invariant forall q: int {:trigger A[q]} :: j < q < N ==> r <= A[q]
      invariant forall p: int, q: int {:trigger A[q], A[p]} :: 0 <= p < m <= q < N ==> A[p] <= A[q]
      invariant forall p: int, q: int {:trigger A[q], A[p]} :: 0 <= p <= n < q < N ==> A[p] <= A[q]
      invariant (i == m && j == n && r == A[f]) || (m < i && j < n)
      decreases j - i
    {
      ghost var firstIteration := i == m && j == n;
      while A[i] < r
        invariant m <= i <= N && (firstIteration ==> i <= f)
        invariant exists g: int {:trigger A[g]} :: i <= g < N && r <= A[g]
        invariant exists g: int {:trigger A[g]} :: 0 <= g <= j && A[g] <= r
        invariant forall p: int {:trigger A[p]} :: 0 <= p < i ==> A[p] <= r
        decreases j - i
      {
        i := i + 1;
      }
      while r < A[j]
        invariant 0 <= j <= n && (firstIteration ==> f <= j)
        invariant exists g: int {:trigger A[g]} :: i <= g < N && r <= A[g]
        invariant exists g: int {:trigger A[g]} :: 0 <= g <= j && A[g] <= r
        invariant forall q: int {:trigger A[q]} :: j < q < N ==> r <= A[q]
        decreases j
      {
        j := j - 1;
      }
      assert A[j] <= r <= A[i];
      if i <= j {
        var w := A[i];
        A[i] := A[j];
        A[j] := w;
        assert A[i] <= r <= A[j];
        i, j := i + 1, j - 1;
      }
    }
    if f <= j {
      n := j;
    } else if 0 <= f {
      m := i;
    } else {
      break;
    }
  }
}
