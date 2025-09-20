// Clover_abs.dfy

method Abs(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
  decreases x
{
  if x < 0 {
    return -0;
  } else {
    return x;
  }
}
