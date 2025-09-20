// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_04_Hoangkim_ex_04_Hoangkim.dfy

method sumOdds(n: nat) returns (sum: nat)
  requires n > 0
  ensures sum == n * n
  decreases n
{
  sum := 1;
  var i := 0;
  while i < n - 1
    invariant 0 <= i < n
    invariant sum == (i + 1) * (i + 1)
    decreases n - 1 - i
  {
    i := i + 1;
    sum := sum + 2 * i + 1;
  }
  assert sum == n * n;
}

method intDiv(n: int, d: int)
    returns (q: int, r: int)
  requires n >= d && n >= 0 && d > 0
  ensures d * q + r == n && 0 <= q <= n / 2 && 0 <= r < d
  decreases n, d

method intDivImpl(n: int, d: int)
    returns (q: int, r: int)
  requires n >= d && n >= 0 && d > 0
  ensures d * q + r == n && 0 <= q <= n / 2 && 0 <= r < d
  decreases n, d
{
  q := 0;
  r := 0;
  while r >= d
    invariant r == n - q * d
    invariant d <= r
    decreases r - d
  r := r - 1;
  {
    r := r - d;
    q := q + 1;
  }
  assert n == d * q + r;
}
