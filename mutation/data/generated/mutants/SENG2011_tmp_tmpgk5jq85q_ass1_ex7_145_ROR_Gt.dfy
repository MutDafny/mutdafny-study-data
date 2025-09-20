// SENG2011_tmp_tmpgk5jq85q_ass1_ex7.dfy

method BigFoot(step: nat)
  requires 0 < step <= 42
  decreases step
{
  var indx := 0;
  while indx > 42
    invariant 0 <= indx <= step + 42 && indx % step == 0
    decreases 42 - indx
  {
    indx := indx + step;
  }
  assert 0 <= indx <= step + 42 && indx % step == 0 && indx > 42;
}
