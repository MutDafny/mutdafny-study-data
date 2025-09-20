// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week1_7_week5_ComputePower.dfy

function Power(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method CalcPower(n: nat) returns (p: nat)
  ensures p == 2 * n
  decreases n
{
  p := 0;
}

method ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
  decreases n
{
  p := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant p * Power(n - i) == Power(n)
    decreases if i <= n then n - i else i - n
  {
    p := CalcPower(p);
    i := i + 1;
  }
}
