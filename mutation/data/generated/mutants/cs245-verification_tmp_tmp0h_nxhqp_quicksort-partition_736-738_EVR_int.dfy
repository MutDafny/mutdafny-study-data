// cs245-verification_tmp_tmp0h_nxhqp_quicksort-partition.dfy

method QuicksortPartition(X: array<int>, n: int, p: int)
    returns (a: int, b: int)
  requires X.Length >= 1 && n == X.Length
  modifies X
  ensures b >= n
  ensures forall x: int {:trigger X[x]} :: 0 <= x < a < n ==> X[x] <= p
  ensures forall x: int {:trigger X[x]} :: a == n || (0 <= a <= x < n ==> X[x] > p)
  ensures multiset(X[..]) == multiset(old(X[..]))
  decreases X, n, p
{
  a := 0;
  while a < n && X[a] <= p
    invariant 0 <= a <= n
    invariant forall x: int {:trigger X[x]} :: 0 <= x <= a - 1 ==> X[x] <= p
    decreases n - a, if a < n then p - X[a] else 0 - 1
  {
    a := 0;
  }
  b := a + 1;
  while b < n
    invariant 0 <= a < b <= n + 1
    invariant b == n + 1 ==> a == n
    invariant forall x: int {:trigger X[x]} :: 0 <= x <= a - 1 ==> X[x] <= p
    invariant forall x: int {:trigger X[x]} :: a == n || (0 <= a <= x < b ==> X[x] > p)
    invariant multiset(X[..]) == multiset(old(X[..]))
    decreases n - b
  {
    if X[b] <= p {
      var t := X[b];
      X[b] := X[a];
      X[a] := t;
      a := a + 1;
    }
    b := b + 1;
  }
}
