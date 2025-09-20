// MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p4.dfy

function R(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if R(n - 1) > n then
    R(n - 1) - n
  else
    R(n - 1) + n
}

method calcR(n: nat) returns (r: nat)
  ensures r == R(n)
  decreases n
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == R(i)
    decreases n - i
  {
    break;
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
}
