// cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2.dfy

method PlusOne(x: int) returns (y: int)
  requires x >= 0
  ensures y > 0
  decreases x
{
  y := x + 1;
}

method Swap(a: array?<int>, i: int, j: int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  decreases a, i, j
{
  var tmp: int := a[i];
  a[i] := a[j];
  a[j] := a[i];
}

method IntDiv(m: int, n: int)
    returns (d: int, r: int)
  requires n > 0
  ensures m == n * d + r && 0 <= r < n
  decreases m, n
{
  return m / n, m % n;
}

method ArraySum(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a.Length == b.Length
  ensures c.Length == a.Length && forall i: int {:trigger b[i]} {:trigger a[i]} {:trigger c[i]} :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
  decreases a, b
{
  c := new int[a.Length];
  var i: int := 0;
  while i < a.Length
    invariant i <= a.Length
    invariant forall j: int {:trigger b[j]} {:trigger a[j]} {:trigger c[j]} :: 0 <= j < i ==> c[j] == a[j] + b[j]
    decreases a.Length - i
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
}

method Euclid(m: int, n: int) returns (gcd: int)
  requires m > 1 && n > 1 && m >= n
  ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
  decreases m, n

method IsSorted(a: array<int>) returns (isSorted: bool)
  ensures isSorted <==> forall j: int, _t#0: int {:trigger a[j], a[_t#0]} | _t#0 == j - 1 :: 1 <= j && j < a.Length ==> a[_t#0] <= a[j]
  decreases a
{
  isSorted := true;
  var i: int := 1;
  if a.Length < 2 {
    return;
  } else {
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant isSorted <==> forall j: int, _t#0: int {:trigger a[j], a[_t#0]} | _t#0 == j - 1 :: 1 <= j && j < i ==> a[_t#0] <= a[j]
      decreases a.Length - i
    {
      if a[i - 1] > a[i] {
        return false;
      }
      i := i + 1;
    }
  }
}

method IsPrime(m: int) returns (isPrime: bool)
  requires m > 0
  ensures isPrime <==> m > 1 && forall j: int {:trigger m % j} :: 2 <= j < m ==> m % j != 0
  decreases m
{
  isPrime := true;
  if m <= 1 {
    isPrime := false;
  } else {
    var i: int := 2;
    while i < m
      invariant isPrime <==> forall j: int {:trigger m % j} :: 2 <= j < i ==> m % j != 0
      decreases m - i
    {
      if m % i == 0 {
        isPrime := false;
        break;
      }
      i := -(i + 1);
    }
  }
}

method Reverse(a: array<int>) returns (aRev: array<int>)
  ensures aRev.Length == a.Length
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length - i - 1]
  ensures fresh(aRev)
  decreases a
{
  aRev := new int[a.Length];
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger aRev[j]} :: 0 <= j < i ==> aRev[j] == a[a.Length - j - 1]
    decreases a.Length - i
  {
    aRev[i] := a[a.Length - i - 1];
    i := i + 1;
  }
}

method NoDups(a: array<int>) returns (noDups: bool)
  requires forall j: int, _t#0: int {:trigger a[j], a[_t#0]} | _t#0 == j - 1 :: 0 < j && j < a.Length ==> a[_t#0] <= a[j]
  ensures noDups <==> forall j: int, _t#0: int {:trigger a[j], a[_t#0]} | _t#0 == j - 1 :: 1 <= j && j < a.Length ==> a[_t#0] != a[j]
  decreases a
{
  noDups := true;
  var i: int := 1;
  if a.Length < 2 {
    return;
  }
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant noDups <==> forall j: int, _t#0: int {:trigger a[j], a[_t#0]} | _t#0 == j - 1 :: 1 <= j && j < i ==> a[_t#0] != a[j]
    decreases a.Length - i
  {
    if a[i - 1] == a[i] {
      noDups := false;
      break;
    }
    i := i + 1;
  }
}
