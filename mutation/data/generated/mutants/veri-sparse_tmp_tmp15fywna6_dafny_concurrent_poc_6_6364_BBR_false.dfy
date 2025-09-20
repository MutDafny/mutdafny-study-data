// veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6.dfy

function sum(s: seq<nat>): nat
  ensures sum(s) == 0 ==> forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] == 0
  decreases s
{
  if s == [] then
    0
  else
    s[0] + sum(s[1..])
}

lemma /*{:_inductionTrigger |s|}*/ /*{:_inductionTrigger sum(s)}*/ /*{:_induction s}*/ sum0(s: seq<nat>)
  ensures sum(s) == 0 ==> forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] == 0
  decreases s
{
  if s == [] {
  } else {
    sum0(s[1..]);
  }
}

lemma /*{:_inductionTrigger sum(s)}*/ /*{:_inductionTrigger |s|}*/ /*{:_induction s}*/ sum_const(s: seq<nat>, x: nat)
  ensures (forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x
  decreases s, x
{
}

lemma /*{:_inductionTrigger sum(s2), sum(s1)}*/ /*{:_inductionTrigger sum(s2), |s1|}*/ /*{:_inductionTrigger sum(s1), |s2|}*/ /*{:_inductionTrigger |s2|, |s1|}*/ /*{:_induction s1, s2}*/ sum_eq(s1: seq<nat>, s2: seq<nat>)
  requires |s1| == |s2|
  requires forall i: int {:trigger s2[i]} {:trigger s1[i]} :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  decreases s1, s2
{
}

lemma /*{:_inductionTrigger sum(s2), sum(s1)}*/ /*{:_inductionTrigger sum(s2), s1[j]}*/ /*{:_inductionTrigger sum(s2), |s1|}*/ /*{:_inductionTrigger sum(s1), s2[j]}*/ /*{:_inductionTrigger sum(s1), |s2|}*/ /*{:_inductionTrigger s2[j], s1[j]}*/ /*{:_inductionTrigger s2[j], |s1|}*/ /*{:_inductionTrigger s1[j], |s2|}*/ /*{:_inductionTrigger |s2|, |s1|}*/ /*{:_induction s1, s2}*/ sum_exept(s1: seq<nat>, s2: seq<nat>, x: nat, j: nat)
  requires |s1| == |s2|
  requires j < |s1|
  requires forall i: int {:trigger s2[i]} {:trigger s1[i]} :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
  requires s1[j] == s2[j] + x
  ensures sum(s1) == sum(s2) + x
  decreases s1, s2, x, j
{
  if s1 == [] {
    assert j >= |s1|;
  } else {
    if j == 0 {
      assert sum(s1) == s1[0] + sum(s1[1..]);
      assert sum(s2) == s2[0] + sum(s2[1..]);
      sum_eq(s1[1..], s2[1..]);
      assert sum(s1[1..]) == sum(s2[1..]);
    } else {
      sum_exept(s1[1..], s2[1..], x, j - 1);
    }
  }
}

function calcRow(M: array2<int>, x: seq<int>, row: nat, start_index: nat): (product: int)
  requires M.Length1 == |x|
  requires row < M.Length0
  requires start_index <= M.Length1
  reads M
  decreases M.Length1 - start_index
{
  if start_index == M.Length1 then
    0
  else
    M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index + 1)
}

method Run(processes: set<Process>, M: array2<int>, x: array<int>)
    returns (y: array<int>)
  requires |processes| == M.Length0
  requires forall p: Process, q: Process {:trigger q.row, p.row} {:trigger q.row, p in processes} {:trigger p.row, q in processes} {:trigger q in processes, p in processes} :: p in processes && q in processes && p != q ==> p.row != q.row
  requires forall p: Process, q: Process {:trigger q in processes, p in processes} :: p in processes && q in processes ==> p != q
  requires forall p: Process {:trigger p.row} {:trigger p in processes} :: (p in processes ==> 0 <= p.row) && (p in processes ==> p.row < M.Length0)
  requires forall p: Process {:trigger p.curColumn} {:trigger p in processes} :: p in processes ==> 0 == p.curColumn
  requires forall p: Process {:trigger p.opsLeft} {:trigger p in processes} :: p in processes ==> p.opsLeft == M.Length1
  requires x.Length > 0
  requires M.Length0 > 0
  requires M.Length1 == x.Length
  modifies processes, M, x
  ensures M.Length0 == y.Length
  decreases processes, M, x
{
  var i := 0;
  y := new int[M.Length0] ((i: nat) => 0);
  var leftOvers := new nat[M.Length0] ((i: nat) => M.Length1);
  var mv := new MatrixVectorMultiplier(processes, M, x[..], y, leftOvers);
  while sum(leftOvers[..]) > 0 && exists p: Process {:trigger p in processes} :: p in processes && false
    invariant mv.Valid(M, x[..], y, processes, leftOvers)
    invariant forall p: Process {:trigger p.curColumn} {:trigger p.row} {:trigger p in processes} :: p in processes ==> y[p.row] + calcRow(M, x[..], p.row, p.curColumn) == calcRow(M, x[..], p.row, 0)
    invariant sum(leftOvers[..]) >= 0
    invariant forall p: Process, q: Process {:trigger q.row, p.row} {:trigger q.row, p in processes} {:trigger p.row, q in processes} {:trigger q in processes, p in processes} :: p in processes && q in processes && p != q ==> p.row != q.row
    decreases sum(leftOvers[..])
  {
    mv.processNext(M, x[..], y, processes, leftOvers);
  }
  assert sum(leftOvers[..]) == 0;
  assert forall i: int {:trigger calcRow(M, x[..], i, 0)} {:trigger y[i]} :: 0 <= i < y.Length ==> y[i] == calcRow(M, x[..], i, 0);
}

class Process {
  var row: nat
  var curColumn: nat
  var opsLeft: nat

  constructor (init_row: nat, initOpsLeft: nat)
    ensures row == init_row
    ensures opsLeft == initOpsLeft
    ensures curColumn == 0
    decreases init_row, initOpsLeft
  {
    row := init_row;
    curColumn := 0;
    opsLeft := initOpsLeft;
  }
}

class MatrixVectorMultiplier {
  ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers: array<nat>)
    reads this, y, P, M, leftOvers
    decreases P + {this, y, M, leftOvers}, M, x, y, P, leftOvers
  {
    M.Length0 == y.Length &&
    M.Length1 == |x| &&
    |P| == y.Length &&
    |P| == leftOvers.Length &&
    (forall p: Process, q: Process {:trigger q.row, p.row} {:trigger q.row, p in P} {:trigger p.row, q in P} {:trigger q in P, p in P} :: 
      p in P &&
      q in P &&
      p != q ==>
        p.row != q.row) &&
    (forall p: Process, q: Process {:trigger q in P, p in P} :: 
      p in P &&
      q in P ==>
        p != q) &&
    (forall p: Process {:trigger p.row} {:trigger p in P} :: 
      (p in P ==>
        0 <= p.row) &&
      (p in P ==>
        p.row < |P|)) &&
    (forall p: Process {:trigger p.curColumn} {:trigger p in P} :: 
      (p in P ==>
        0 <= p.curColumn) &&
      (p in P ==>
        p.curColumn <= M.Length1)) &&
    (forall p: Process {:trigger p.opsLeft} {:trigger p in P} :: 
      (p in P ==>
        0 <= p.opsLeft) &&
      (p in P ==>
        p.opsLeft <= M.Length1)) &&
    (forall p: Process {:trigger p.curColumn} {:trigger p.row} {:trigger p in P} :: 
      p in P ==>
        y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)) &&
    (forall p: Process {:trigger p.opsLeft} {:trigger p.row} {:trigger p in P} :: 
      p in P ==>
        leftOvers[p.row] == p.opsLeft) &&
    (forall p: Process {:trigger p.curColumn} {:trigger p.opsLeft} {:trigger p in P} :: 
      p in P ==>
        p.opsLeft == M.Length1 - p.curColumn) &&
    (sum(leftOvers[..]) > 0 ==>
      exists p: Process {:trigger p.opsLeft} {:trigger p in P} :: 
        p in P &&
        p.opsLeft > 0)
  }

  constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers: array<nat>)
    requires forall i: int {:trigger leftOvers[i]} :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1
    requires |processes| == leftOvers.Length
    requires |processes| == M_.Length0
    requires forall p: Process, q: Process {:trigger q.row, p.row} {:trigger q.row, p in processes} {:trigger p.row, q in processes} {:trigger q in processes, p in processes} :: p in processes && q in processes && p != q ==> p.row != q.row
    requires forall p: Process, q: Process {:trigger q in processes, p in processes} :: p in processes && q in processes ==> p != q
    requires forall p: Process {:trigger p.row} {:trigger p in processes} :: (p in processes ==> 0 <= p.row) && (p in processes ==> p.row < M_.Length0)
    requires forall p: Process {:trigger p.curColumn} {:trigger p in processes} :: p in processes ==> 0 == p.curColumn
    requires forall p: Process {:trigger p.opsLeft} {:trigger p in processes} :: p in processes ==> p.opsLeft == M_.Length1
    requires forall i: int {:trigger y_[i]} :: 0 <= i < y_.Length ==> y_[i] == 0
    requires y_.Length == M_.Length0
    requires |x_| == M_.Length1
    requires M_.Length0 > 0
    requires |x_| > 0
    ensures forall i: int {:trigger leftOvers[i]} :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1
    ensures Valid(M_, x_, y_, processes, leftOvers)
    decreases processes, M_, x_, y_, leftOvers
  {
  }

  method processNext(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers: array<nat>)
    requires Valid(M, x, y, P, leftOvers)
    requires exists p: Process {:trigger p.opsLeft} {:trigger p in P} :: p in P && p.opsLeft > 0
    requires sum(leftOvers[..]) > 0
    requires forall p: Process, q: Process {:trigger q.row, p.row} {:trigger q.row, p in P} {:trigger p.row, q in P} {:trigger q in P, p in P} :: p in P && q in P && p != q ==> p.row != q.row
    modifies this, y, P, leftOvers
    ensures Valid(M, x, y, P, leftOvers)
    ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    decreases M, x, y, P, leftOvers
  {
    var p :| p in P && p.opsLeft > 0;
    y[p.row] := y[p.row] + M[p.row, p.curColumn] * x[p.curColumn];
    p.opsLeft := p.opsLeft - 1;
    p.curColumn := p.curColumn + 1;
    leftOvers[p.row] := leftOvers[p.row] - 1;
    assert forall i: int {:trigger old(leftOvers[i])} {:trigger leftOvers[i]} :: 0 <= i < leftOvers.Length ==> i != p.row ==> leftOvers[i] == old(leftOvers[i]);
    assert leftOvers[p.row] + 1 == old(leftOvers[p.row]);
    assert forall p: Process {:trigger p.opsLeft} {:trigger p.row} {:trigger p in P} :: p in P ==> leftOvers[p.row] == p.opsLeft;
    sum_exept(old(leftOvers[..]), leftOvers[..], 1, p.row);
  }
}
