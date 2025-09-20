// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_05_Hoangkim_ex_05_Hoangkim.dfy

function fib(n: nat): nat
  decreases n
{
  if n < 2 then
    n
  else
    fib(n - 2) + fib(n - 1)
}

method fibIter(n: nat) returns (a: nat)
  requires n > 0
  ensures a == fib(n)
  decreases n
{
  a := -1;
  var b, x := 1, 0;
  while x < n
    invariant 0 <= x <= n
    invariant a == fib(x)
    invariant b == fib(x + 1)
    decreases n - x
  {
    a, b := b, a + b;
    x := x + 1;
  }
  assert a == fib(n);
}

function fact(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

method factIter(n: nat) returns (a: nat)
  requires n >= 0
  ensures a == fact(n)
  decreases n
{
  a := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant a == fact(i - 1)
    decreases n - i
  {
    a := a * i;
    i := i + 1;
  }
  assert a == fact(n);
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
  decreases m, n
{
  if m == n then
    m
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}

method gcdI(m: int, n: int) returns (g: int)
  requires m > 0 && n > 0
  ensures g == gcd(m, n)
  decreases m, n
{
  var x: int;
  g := m;
  x := n;
  while g != x
    invariant x > 0
    invariant g > 0
    invariant gcd(g, x) == gcd(m, n)
    decreases x + g
  {
    if g > x {
      g := g - x;
    } else {
      x := x - g;
    }
  }
}
