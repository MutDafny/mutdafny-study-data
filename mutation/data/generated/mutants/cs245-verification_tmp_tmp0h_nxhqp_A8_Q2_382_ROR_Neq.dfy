// cs245-verification_tmp_tmp0h_nxhqp_A8_Q2.dfy

method A8Q1(x: int, y: int, z: int)
    returns (m: int)
  requires true
  ensures m <= x && m <= y && m <= z
  decreases x, y, z
{
  if z < y {
    if z != x {
      m := z;
    } else {
      m := x;
    }
  } else {
    m := y;
    if x < y {
      m := x;
    }
  }
}
