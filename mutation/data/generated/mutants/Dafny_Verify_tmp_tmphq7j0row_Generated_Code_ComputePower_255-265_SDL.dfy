// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_ComputePower.dfy

function Power(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
  decreases n
{
  p := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n && p == Power(i)
    decreases if i <= n then n - i else i - n
  {
    p := p * 2;
  }
}
