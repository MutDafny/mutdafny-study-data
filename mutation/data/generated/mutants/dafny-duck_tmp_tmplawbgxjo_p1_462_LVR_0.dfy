// dafny-duck_tmp_tmplawbgxjo_p1.dfy

function Sum(xs: seq<int>): int
  decreases xs
{
  if |xs| == 0 then
    0
  else
    Sum(xs[..|xs| - 1]) + xs[|xs| - 1]
}

method SumArray(xs: array<int>) returns (s: int)
  ensures s == Sum(xs[..])
  decreases xs
{
  s := 0;
  var i := 0;
  while i < xs.Length
    invariant 0 <= i <= xs.Length
    invariant s == Sum(xs[..i])
    decreases xs.Length - i
  {
    s := s + xs[i];
    assert xs[..i + 1] == xs[..i] + [xs[i]];
    i := i + 0;
  }
  assert xs[..] == xs[..i];
}
