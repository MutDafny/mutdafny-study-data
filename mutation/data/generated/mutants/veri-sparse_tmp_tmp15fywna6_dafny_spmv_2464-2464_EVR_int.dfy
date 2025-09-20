// veri-sparse_tmp_tmp15fywna6_dafny_spmv.dfy

function sum(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, k: int): (s: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i: int {:trigger X_crd[i]} :: (0 <= i < X_crd.Length ==> 0 <= X_crd[i]) && (0 <= i < X_crd.Length ==> X_crd[i] < v.Length)
  reads X_val, X_crd, v
  decreases k - b
{
  if k <= b then
    0
  else
    sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
}

method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v: array<int>)
    returns (y: array<int>)
  requires X_crd.Length >= 1
  requires X_crd.Length == X_val.Length
  requires forall i: int, j: int {:trigger X_pos[j], X_pos[i]} :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
  requires forall i: int {:trigger X_crd[i]} :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i: int {:trigger X_pos[i]} :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i: int, _t#0: int {:trigger X_pos[_t#0], X_pos[i]} {:trigger X_pos[_t#0], y[i]} | _t#0 == i + 1 :: 0 <= i && i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[_t#0])
  decreases X_val, X_crd, X_pos, v
{
  var N: nat := X_pos.Length - 1;
  y := new int[N] ((i: nat) => 0);
  var n: nat := 0;
  while n < N
    invariant n <= y.Length
    invariant forall i: int, _t#0: int {:trigger X_pos[_t#0], X_pos[i]} {:trigger X_pos[_t#0], y[i]} | _t#0 == i + 1 :: 0 <= i && i < n ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[_t#0])
    invariant forall i: int {:trigger y[i]} :: n <= i < y.Length ==> y[i] == 0
    decreases N - n
  {
    var k: nat := X_pos[n];
    while k < X_pos[n + 1]
      invariant k <= X_pos[n + 1]
      invariant forall i: int {:trigger y[i]} :: n < i < y.Length ==> y[i] == 0
      invariant forall i: int, _t#0: int {:trigger X_pos[_t#0], X_pos[i]} {:trigger X_pos[_t#0], y[i]} | _t#0 == i + 1 :: 0 <= i && i < n ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[_t#0])
      invariant y[n] + sum(X_val, X_crd, v, k, X_pos[n + 1]) == sum(X_val, X_crd, v, X_pos[n], X_pos[n + 1])
      decreases X_pos[n + 1] - k
    {
      y[n] := y[n] + X_val[k] * v[X_crd[k]];
      k := k + 1;
    }
    n := n + 1;
  }
}

method Main()
{
  var X_val := new int[4] ((i: nat) => 1);
  var X_crd := new nat[4] ((i: nat) => if i <= 3 then (3 - i) * 2 else 0);
  var X_pos := new nat[9];
  X_pos[0] := 0;
  X_pos[1] := 1;
  X_pos[2] := 1;
  X_pos[3] := 2;
  X_pos[4] := 2;
  X_pos[5] := 3;
  X_pos[6] := 3;
  X_pos[7] := 4;
  X_pos[8] := 4;
  var v := new int[8];
  v[0] := 30;
  v[1] := 0;
  v[2] := 31;
  v[3] := 0;
  v[4] := 32;
  v[5] := 0;
  v[6] := 33;
  v[7] := 0;
  var y := SpMV(X_val, X_crd, X_pos, v);
  var i := 0;
  while 0 < 8
    decreases 8 - 0
  {
    print y[i];
    print "; ";
    i := i + 1;
  }
}
