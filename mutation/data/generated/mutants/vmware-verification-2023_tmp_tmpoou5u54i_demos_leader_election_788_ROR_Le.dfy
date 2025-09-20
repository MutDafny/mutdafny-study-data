// vmware-verification-2023_tmp_tmpoou5u54i_demos_leader_election.dfy

ghost predicate Init(c: Constants, v: Variables)
  decreases c, v
{
  v.WF(c) &&
  c.UniqueIds() &&
  forall i: int {:trigger v.highest_heard[i]} {:trigger c.ValidIdx(i)} | c.ValidIdx(i) :: 
    v.highest_heard[i] == -1
}

function max(a: int, b: int): int
  decreases a, b
{
  if a <= b then
    a
  else
    b
}

function NextIdx(c: Constants, idx: nat): nat
  requires c.WF()
  requires c.ValidIdx(idx)
  decreases c, idx
{
  if idx + 1 == |c.ids| then
    0
  else
    idx + 1
}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
  decreases c, v, v', srcidx
{
  v.WF(c) &&
  v'.WF(c) &&
  c.ValidIdx(srcidx) &&
  ghost var dstidx: nat := NextIdx(c, srcidx); true && ghost var message: int := max(v.highest_heard[srcidx], c.ids[srcidx]); true && ghost var dst_new_max: int := max(v.highest_heard[dstidx], message); true && v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  decreases c, v, v', step
{
  match step {
    case TransmissionStep(srcidx) =>
      Transmission(c, v, v', srcidx)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
  decreases c, v, v'
{
  exists step: Step {:trigger NextStep(c, v, v', step)} :: 
    NextStep(c, v, v', step)
}

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
  decreases c, v, i
{
  c.ValidIdx(i) &&
  v.highest_heard[i] == c.ids[i]
}

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall i: int, j: int {:trigger IsLeader(c, v, j), IsLeader(c, v, i)} | IsLeader(c, v, i) && IsLeader(c, v, j) :: 
    i == j
}

ghost predicate IsChord(c: Constants, v: Variables, start: int, end: int)
  decreases c, v, start, end
{
  v.WF(c) &&
  c.ValidIdx(start) &&
  c.ValidIdx(end) &&
  c.ids[start] == v.highest_heard[end]
}

ghost predicate Between(start: int, node: int, end: int)
  decreases start, node, end
{
  if start < end then
    start < node < end
  else
    node < end || start < node
}

ghost predicate OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c)
  decreases c, v, start, end
{
  forall node: int {:trigger c.ids[node]} {:trigger v.highest_heard[node]} {:trigger c.ValidIdx(node)} {:trigger Between(start, node, end)} | Between(start, node, end) && c.ValidIdx(node) :: 
    v.highest_heard[node] > c.ids[node]
}

ghost predicate OnChordHeardDominatesIdInv(c: Constants, v: Variables)
  decreases c, v
{
  v.WF(c) &&
  forall start: int, end: int {:trigger OnChordHeardDominatesId(c, v, start, end)} {:trigger IsChord(c, v, start, end)} | IsChord(c, v, start, end) :: 
    OnChordHeardDominatesId(c, v, start, end)
}

ghost predicate Inv(c: Constants, v: Variables)
  decreases c, v
{
  v.WF(c) &&
  OnChordHeardDominatesIdInv(c, v) &&
  Safety(c, v)
}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
  decreases c, v
{
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
  decreases c, v, v'
{
  ghost var step :| NextStep(c, v, v', step);
  ghost var srcidx := step.srcidx;
  ghost var dstidx := NextIdx(c, srcidx);
  ghost var message := max(v.highest_heard[srcidx], c.ids[srcidx]);
  ghost var dst_new_max := max(v.highest_heard[dstidx], message);
  forall start: int, end: int | IsChord(c, v', start, end)
    ensures OnChordHeardDominatesId(c, v', start, end)
  {
    forall node: int | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      if dstidx == end {
        if v'.highest_heard[end] == v.highest_heard[end] {
          assert v' == v;
        } else if v'.highest_heard[end] == c.ids[srcidx] {
          assert false;
        } else if v'.highest_heard[end] == v.highest_heard[srcidx] {
          assert IsChord(c, v, start, srcidx);
        }
      } else {
        assert IsChord(c, v, start, end);
      }
    }
  }
  assert OnChordHeardDominatesIdInv(c, v');
  forall i: int, j: int | IsLeader(c, v', i) && IsLeader(c, v', j)
    ensures i == j
  {
    assert IsChord(c, v', i, i);
    assert IsChord(c, v', j, j);
  }
  assert Safety(c, v');
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
  decreases c, v
{
}

datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: int)
    decreases this, i
  {
    0 <= i < |ids|
  }

  ghost predicate UniqueIds()
    decreases this
  {
    forall i: int, j: int {:trigger ids[j], ids[i]} {:trigger ids[j], ValidIdx(i)} {:trigger ids[i], ValidIdx(j)} {:trigger ValidIdx(j), ValidIdx(i)} | ValidIdx(i) && ValidIdx(j) && ids[i] == ids[j] :: 
      i == j
  }

  ghost predicate WF()
    decreases this
  {
    0 < |ids| &&
    UniqueIds()
  }
}

datatype Variables = Variables(highest_heard: seq<int>) {
  ghost predicate WF(c: Constants)
    decreases this, c
  {
    c.WF() &&
    |highest_heard| == |c.ids|
  }
}

datatype Step = TransmissionStep(srcidx: nat)
