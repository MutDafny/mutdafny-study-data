// t1_MF_tmp_tmpi_sqie4j_exemplos_colecoes_conjuntos_ex5.dfy

function to_seq<T>(a: array<T>, i: int): (res: seq<T>)
  requires 0 <= i <= a.Length
  reads a
  ensures res == a[i..]
  decreases a.Length - i
{
  if i == a.Length then
    []
  else
    [a[i]] + to_seq(a, i + 1)
}

method Main()
{
  var a: array<int> := new int[2];
  a[0] := 2;
  var ms: multiset<int> := multiset(a[..]);
  assert a[..] == to_seq(a, 0);
  assert ms[2] == 1;
}
