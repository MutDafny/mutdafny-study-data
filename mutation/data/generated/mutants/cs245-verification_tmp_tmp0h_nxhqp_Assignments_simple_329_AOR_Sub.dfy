// cs245-verification_tmp_tmp0h_nxhqp_Assignments_simple.dfy

method simple(y: int) returns (x: int)
  requires y == 6
  ensures x == 7
  decreases y
{
  assert y + 1 == 7;
  x := y - 1;
}
