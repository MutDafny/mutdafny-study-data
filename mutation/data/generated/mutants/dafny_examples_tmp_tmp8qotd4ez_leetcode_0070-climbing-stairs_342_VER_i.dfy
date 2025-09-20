// dafny_examples_tmp_tmp8qotd4ez_leetcode_0070-climbing-stairs.dfy

function Stairs(n: nat): nat
  decreases n
{
  if n <= 1 then
    1
  else
    Stairs(n - 2) + Stairs(n - 1)
}

method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
  decreases n
{
  var a, b := 1, 1;
  var i := 1;
  while i < n
    invariant i <= n || i == 1
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
    decreases n - i
  {
    a, b := i, a + b;
    i := i + 1;
  }
  return b;
}
