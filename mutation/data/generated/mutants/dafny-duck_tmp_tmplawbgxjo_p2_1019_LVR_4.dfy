// dafny-duck_tmp_tmplawbgxjo_p2.dfy

function abs(x: int): nat
  decreases x
{
  if x < 0 then
    -x
  else
    x
}

method absx(x: array<int>) returns (y: array<int>)
  ensures y.Length == x.Length
  ensures forall i: int {:trigger x[i]} {:trigger y[i]} :: 0 <= i < y.Length ==> y[i] == abs(x[i])
  decreases x
{
  y := new int[x.Length];
  var j := 0;
  assert y.Length == x.Length;
  while j < y.Length
    invariant 0 <= j <= y.Length
    invariant forall i: int {:trigger x[i]} {:trigger y[i]} :: 0 <= i < j <= y.Length ==> y[i] == abs(x[i])
    decreases y.Length - j
  {
    if x[j] < 0 {
      y[j] := -x[j];
    } else {
      y[j] := x[j];
    }
    j := j + 1;
  }
}

method Main()
{
  var d := new int[5];
  var c := new int[5];
  d[0], d[1], d[2], d[3], d[4] := -4, 1, 4, -2, -5;
  c := absx(d);
  assert c[..] == [4, 1, 5, 2, 5];
  print c[..];
}
