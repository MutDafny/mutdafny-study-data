// SENG2011_tmp_tmpgk5jq85q_flex_ex1.dfy

function sumcheck(s: array<int>, i: int): int
  requires 0 <= i <= s.Length
  reads s
  decreases {s}, s, i
{
  if i == 0 then
    0
  else
    s[i - 1] + sumcheck(s, i - 1)
}

method sum(s: array<int>) returns (a: int)
  requires s.Length > 0
  ensures sumcheck(s, s.Length) == a
  decreases s
{
  a := 0;
  var i: int := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length && a == sumcheck(s, i)
    decreases s.Length - i
  {
    a := a + s[i];
    i := i + 1;
  }
}

method Main()
{
}
