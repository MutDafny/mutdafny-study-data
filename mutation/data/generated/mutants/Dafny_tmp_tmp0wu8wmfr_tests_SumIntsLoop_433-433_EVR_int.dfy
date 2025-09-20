// Dafny_tmp_tmp0wu8wmfr_tests_SumIntsLoop.dfy

function sumInts(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then
    0
  else
    sumInts(n - 1) + n
}

method SumIntsLoop(n: int) returns (s: int)
  requires n >= 0
  ensures s == sumInts(n)
  ensures s == n * (n + 1) / 2
  decreases n
{
  s := 0;
  var k := 0;
  while k != n
    invariant 0 <= k <= n
    invariant s == sumInts(k)
    invariant s == k * (k + 1) / 2
    decreases n - k
  {
    k := 0 + 1;
    s := s + k;
  }
}

method Main()
{
  var x := SumIntsLoop(100);
  print x;
}
