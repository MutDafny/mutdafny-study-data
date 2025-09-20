// t1_MF_tmp_tmpi_sqie4j_exemplos_introducao_ex4.dfy

function Fat(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}

method Fatorial(n: nat) returns (r: nat)
  ensures r == Fat(n)
  decreases n
{
  r := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == Fat(i)
    decreases n - i
  {
    i := i + 1;
    r := r;
  }
}
