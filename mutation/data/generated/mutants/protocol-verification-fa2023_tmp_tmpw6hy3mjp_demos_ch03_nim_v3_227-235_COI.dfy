// protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_ch03_nim_v3.dfy

ghost predicate Init(v: Variables)
  decreases v
{
  |v.piles| == 3 &&
  v.turn.P1?
}

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
  decreases v, v', step
{
  ghost var p: nat := step.p;
  ghost var take: nat := step.take;
  p < |v.piles| &&
  take <= v.piles[p] &&
  v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  decreases v, v', step
{
  match step {
    case TurnStep(_ /* _v0 */, _ /* _v1 */) =>
      Turn(v, v', step)
    case NoOpStep() =>
      v' == v
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
  decreases v, v', v'', step
{
}

ghost predicate Next(v: Variables, v': Variables)
  decreases v, v'
{
  exists step: Step {:trigger NextStep(v, v', step)} :: 
    NextStep(v, v', step)
}

lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| >= 3
  ensures Init(b[0])
  ensures forall i: nat, _t#0: int {:trigger b[_t#0], b[i]} | _t#0 == i + 1 && _t#0 < |b| :: Next(b[i], b[_t#0])
{
  ghost var state0 := Variables(piles := [3, 5, 7], turn := P1);
  b := [state0, Variables(piles := [3, 1, 7], turn := P2), Variables(piles := [3, 1, 0], turn := P1)];
  assert NextStep(b[0], b[1], TurnStep(take := 4, p := 1));
  assert NextStep(b[1], b[2], TurnStep(take := 7, p := 2));
}

datatype Player = P1 | P2 {
  function Other(): Player
    decreases this
  {
    if !(this == P1) then
      P2
    else
      P1
  }
}

datatype Variables = Variables(piles: seq<nat>, turn: Player)

datatype Step = TurnStep(take: nat, p: nat) | NoOpStep
