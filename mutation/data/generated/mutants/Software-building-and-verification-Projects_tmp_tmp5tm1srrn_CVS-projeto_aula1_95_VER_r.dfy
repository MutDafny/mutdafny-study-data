// Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula1.dfy

method factImp(n: int) returns (r: int)
  decreases n
{
  r := 1;
  var m := n;
  while m > 0
    decreases m - 0
  {
    r := r * r;
    m := m - 1;
  }
}

function power(n: int, m: nat): int
  decreases n, m
{
  if m == 0 then
    1
  else
    n * power(n, m - 1)
}

function pow(n: int, m: nat, r: int): int
  decreases n, m, r
{
  if m == 0 then
    r
  else
    pow(n, m - 1, r * n)
}

function powerAlt(n: int, m: nat): int
  decreases n, m
{
  pow(n, m, 1)
}

function equivalentes(n: int, m: nat, r: int): int
  ensures power(n, m) == pow(n, m, r)
  decreases n, m, r

lemma l1(n: int, m: nat, r: int)
  ensures equivalentes(n, m, r) == powerAlt(n, m)
  decreases n, m, r

function fact(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

function factAcc(n: nat, a: int): int
  decreases n
{
  if n == 0 then
    a
  else
    factAcc(n - 1, n * a)
}

function factAlt(n: nat): int
  decreases n
{
  factAcc(n, 1)
}

lemma factAcc_correct(n: nat, a: int)
  ensures factAcc(n, a) == fact(n) * a
  decreases n, a

lemma /*{:_inductionTrigger factAlt(n)}*/ /*{:_inductionTrigger fact(n)}*/ /*{:_induction n}*/ equiv(n: nat)
  ensures fact(n) == factAlt(n)
  decreases n
{
  factAcc_correct(n, 1);
  assert factAcc(n, 1) == fact(n) * 1;
  assert factAlt(n) == factAcc(n, 1);
  assert fact(n) == fact(n) * 1;
}

function mystery1(n: nat, m: nat): nat
  ensures mystery1(n, m) == n + m
  decreases n, m
{
  if n == 0 then
    m
  else
    mystery1(n - 1, m + 1)
}

function mystery2(n: nat, m: nat): nat
  ensures mystery2(n, m) == n + m
  decreases m
{
  if m == 0 then
    n
  else
    mystery2(n + 1, m - 1)
}

function mystery3(n: nat, m: nat): nat
  ensures mystery3(n, m) == n * m
  decreases n, m
{
  if n == 0 then
    0
  else
    mystery1(m, mystery3(n - 1, m))
}

function mystery4(n: nat, m: nat): nat
  ensures mystery4(n, m) == power(n, m)
  decreases n, m
{
  if m == 0 then
    1
  else
    mystery3(n, mystery4(n, m - 1))
}
