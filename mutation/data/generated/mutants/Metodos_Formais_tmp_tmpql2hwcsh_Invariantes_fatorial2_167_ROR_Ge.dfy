// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_fatorial2.dfy

function Fat(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}

method Fatorial(n: nat) returns (f: nat)
  ensures f == Fat(n)
  decreases n
{
  f := 1;
  var i := 1;
  while i >= n
    invariant 1 <= i <= n + 1
    invariant f == Fat(i - 1)
    decreases n - i
  {
    f := f * i;
    i := i + 1;
  }
  return f;
}
