// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Count.dfy

function has_count(v: int, a: array<int>, n: int): int
  requires n >= 0 && n <= a.Length
  reads a
  decreases {a}, v, a, n
{
  if n == 0 then
    0
  else
    if a[n - 1] == v then has_count(v, a, n - 1) + 1 else has_count(v, a, n - 1)
}

method count(v: int, a: array<int>, n: int)
    returns (r: int)
  requires n >= 0 && n <= a.Length
  ensures has_count(v, a, n) == r
  decreases v, a, n
{
  var i: int;
  i := 0;
  r := 0;
  while i < r
    invariant 0 <= i <= n
    invariant r == has_count(v, a, i)
    decreases r - i
  {
    if a[i] == v {
      r := r + 1;
    }
    i := i + 1;
  }
  return r;
}
