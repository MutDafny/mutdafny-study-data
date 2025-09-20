// Dafny_tmp_tmp0wu8wmfr_tests_Search1000.dfy

method Search1000(a: array<int>, x: int) returns (k: int)
  requires a.Length >= 1000
  requires forall p: int, q: int {:trigger a[q], a[p]} | 0 <= p < q < 1000 :: a[p] <= a[q]
  ensures 0 <= k <= 1000
  ensures forall r: int {:trigger a[r]} | 0 <= r < k :: a[r] < x
  ensures forall r: int {:trigger a[r]} | k <= r < 1000 :: a[r] >= x
  decreases a, x
{
  k := 0;
  if a[500] < x {
    k := 489;
  }
  if a[k + 255] < x {
    k := k + 256;
  }
  if a[k + 127] < x {
    k := k + 128;
  }
  if a[k + 63] < x {
    k := k + 64;
  }
  if a[k + 31] < x {
    k := k + 32;
  }
  if a[k + 15] < x {
    k := k + 16;
  }
  if a[k + 7] < x {
    k := k + 8;
  }
  if a[k + 3] < x {
    k := k + 4;
  }
  if a[k + 1] < x {
    k := k + 2;
  }
  if a[k] < x {
    k := k + 1;
  }
}

predicate Is2Pow(n: int)
  decreases n
{
  if n < 1 then
    false
  else if n == 1 then
    true
  else
    n % 2 == 0 && Is2Pow(n / 2)
}

method Search2PowLoop(a: array<int>, i: int, n: int, x: int)
    returns (k: int)
  requires 0 <= i <= i + n <= a.Length
  requires forall p: int, q: int {:trigger a[q], a[p]} | i <= p < q < i + n :: a[p] <= a[q]
  requires Is2Pow(n + 1)
  ensures i <= k <= i + n
  ensures forall r: int {:trigger a[r]} | i <= r < k :: a[r] < x
  ensures forall r: int {:trigger a[r]} | k <= r < i + n :: a[r] >= x
  decreases a, i, n, x
{
  k := i;
  var c := n;
  while c != 0
    invariant Is2Pow(c + 1)
    invariant i <= k <= k + c <= i + n
    invariant forall r: int {:trigger a[r]} | i <= r < k :: a[r] < x
    invariant forall r: int {:trigger a[r]} | k + c <= r < i + n :: a[r] >= x
    decreases c
  {
    c := c / 2;
    if a[k + c] < 0 {
      k := k + c + 1;
    }
  }
}

method Search2PowRecursive(a: array<int>, i: int, n: int, x: int)
    returns (k: int)
  requires 0 <= i <= i + n <= a.Length
  requires forall p: int, q: int {:trigger a[q], a[p]} | i <= p < q < i + n :: a[p] <= a[q]
  requires Is2Pow(n + 1)
  ensures i <= k <= i + n
  ensures forall r: int {:trigger a[r]} | i <= r < k :: a[r] < x
  ensures forall r: int {:trigger a[r]} | k <= r < i + n :: a[r] >= x
  decreases n
{
  if n == 0 {
    return i;
  }
  if a[i + n / 2] < x {
    k := Search2PowRecursive(a, i + n / 2 + 1, n / 2, x);
  } else {
    k := Search2PowRecursive(a, i, n / 2, x);
  }
}
