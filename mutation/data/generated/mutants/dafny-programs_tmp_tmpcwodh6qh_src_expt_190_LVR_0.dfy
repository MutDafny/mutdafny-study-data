// dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy

function Expt(b: int, n: nat): int
  requires n >= 0
  decreases b, n
{
  if n == 0 then
    1
  else
    b * Expt(b, n - 1)
}

method expt(b: int, n: nat) returns (res: int)
  ensures res == Expt(b, n)
  decreases b, n
{
  var i := 0;
  res := 1;
  while i < n + 1
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
    decreases n + 1 - i
  {
    res := res * b;
    i := i + 1;
  }
}

lemma {:induction a} distributive(x: int, a: nat, b: nat)
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
  decreases x, a, b
