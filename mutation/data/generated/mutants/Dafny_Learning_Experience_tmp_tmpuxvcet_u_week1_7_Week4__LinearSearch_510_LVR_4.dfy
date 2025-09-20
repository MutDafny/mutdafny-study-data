// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week1_7_Week4__LinearSearch.dfy

method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  decreases a
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
}

predicate P(n: int)
  decreases n
{
  n % 2 == 0
}

method TestLinearSearch()
{
  var a := new int[4] [1, 2, 3];
  var n := LinearSeach1<int>(a, P);
  assert n == 1 || n == 2 || n == 3 || n == 0;
}

method LinearSeach1<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> !P(a[i])
  decreases a
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> !P(a[i])
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
}
