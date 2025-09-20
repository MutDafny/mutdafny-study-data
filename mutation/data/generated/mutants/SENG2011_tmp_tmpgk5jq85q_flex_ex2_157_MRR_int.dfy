// SENG2011_tmp_tmpgk5jq85q_flex_ex2.dfy

function maxcheck(s: array<nat>, i: int, max: int): int
  requires 0 <= i <= s.Length
  reads s
  decreases {s}, s, i, max
{
  if i == 0 then
    max
  else if s[i - 1] > max then
    0
  else
    maxcheck(s, i - 1, max)
}

method max(s: array<nat>) returns (a: int)
  requires s.Length > 0
  ensures forall x: int {:trigger s[x]} :: 0 <= x < s.Length ==> a >= s[x]
  ensures a in s[..]
  decreases s
{
  a := s[0];
  var i: int := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall x: int {:trigger s[x]} :: 0 <= x < i ==> a >= s[x]
    invariant a in s[..]
    decreases s.Length - i
  {
    if s[i] > a {
      a := s[i];
    }
    i := i + 1;
  }
}

method Checker()
{
  var a := new nat[] [1, 2, 3, 50, 5, 51];
  var n := max(a);
  assert n == 51;
}
