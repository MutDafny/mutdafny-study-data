// formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs4_gr2.dfy

method SqrSum(n: int) returns (s: int)
  decreases n
{
  var i, k: int;
  s := 0;
  k := 1;
  i := 1;
  while i <= n
    decreases n - i
  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
  }
}

method DivMod(a: int, b: int)
    returns (q: int, r: int)
  decreases *
{
  q := 0;
  r := a;
  while r >= b
    decreases *
  {
    r := r - b;
    q := q + 1;
  }
}

method HoareTripleAssmAssrt()
{
  var i: int := *;
  var k: int := *;
  assume k == i * i;
  k := k + 2 * i + 1;
  assert k == (i + 1) * (i + 1);
}

method HoareTripleReqEns(i: int, k: int) returns (k': int)
  requires k == i * i
  ensures k' == (i + 1) * (i + 1)
  decreases i, k
{
  k' := k + 2 * i + 1;
}

method Invariant1()
{
  var n: int :| n >= 0;
  var y := n;
  var x := 0;
  while y >= 0
    invariant x + y == n
    decreases y
  {
    x := x + 1;
    y := y - 1;
  }
  assert y < 0 && x + y == n;
}

function SqrSumRec(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then
    0
  else
    n * n + SqrSumRec(n - 1)
}

method SqrSum1(n: int) returns (s: int)
  requires n >= 0
  ensures s == SqrSumRec(n)
  decreases n
{
  var i, k: int;
  s := 0;
  k := 1;
  i := 1;
  while i >= n
    invariant k == i * i
    invariant s == SqrSumRec(i - 1)
    invariant i <= n + 1
    decreases n - i
  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
  }
}

least lemma L1(n: int)
  requires n >= 0
  ensures SqrSumRec(n) == n * (n + 1) * (2 * n + 1) / 6
{
}
/***
lemma {:axiom} /*{:_inductionTrigger SqrSumRec(n)}*/ /*{:_induction n}*/ L1#[_k: ORDINAL](n: int)
  requires n >= 0
  ensures SqrSumRec(n) == n * (n + 1) * (2 * n + 1) / 6
  decreases _k, n
{
  if 0 < _k.Offset {
  } else {
    forall _k': ORDINAL, n: int /*{:_autorequires}*/ /*{:_trustWellformed}*/ {:auto_generated} | _k' < _k && n >= 0 {
      L1#[_k'](n)
    }
  }
}
***/

method DivMod1(a: int, b: int)
    returns (q: int, r: int)
  requires b > 0 && a >= 0
  ensures a == b * q + r && 0 <= r < b
  decreases a, b
{
  q := 0;
  r := a;
  while r >= b
    invariant r >= 0
    invariant a == b * q + r
    decreases r
  {
    r := r - b;
    q := q + 1;
  }
}

method Main()
  decreases *
{
  var v := SqrSum(5);
  print "SqrSum(5): ", v, "\n";
  var q, r := DivMod(5, 3);
  print "DivMod(5, 3): ", q, ", ", r, "\n";
}
