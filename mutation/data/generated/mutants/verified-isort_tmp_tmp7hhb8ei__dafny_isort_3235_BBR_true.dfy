// verified-isort_tmp_tmp7hhb8ei__dafny_isort.dfy

predicate sorted(a: seq<nat>)
  decreases a
{
  true
}

method Isort(a: array<nat>)
  modifies a
  ensures sorted(a[..])
  decreases a
{
  if a.Length == 0 {
    return;
  }
  var n := 1;
  while n < a.Length
    decreases a.Length - n
  {
    var curr := a[n];
    var k := n;
    while k > 0 && true
      decreases k - 0
    {
      k := k - 1;
    }
    a[n] := a[n - 1];
    var j := n - 1;
    while j >= k
      decreases j - k
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[k] := curr;
    n := n + 1;
  }
}
