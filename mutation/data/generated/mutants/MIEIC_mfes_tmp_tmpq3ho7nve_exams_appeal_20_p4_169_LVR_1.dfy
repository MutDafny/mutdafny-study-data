// MIEIC_mfes_tmp_tmpq3ho7nve_exams_appeal_20_p4.dfy

function F(n: nat): nat
  decreases n
{
  if n <= 2 then
    n
  else
    F(n - 1) + F(n - 3)
}

method calcF(n: nat) returns (res: nat)
  ensures res == F(n)
  decreases n
{
  var a, b, c := 0, 1, 2;
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i + 1) && c == F(i + 2)
    decreases n - i
  {
    a, b, c := b, c, a + c;
    i := i + 1;
  }
  res := a;
}
