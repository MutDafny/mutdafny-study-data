// Clover_min_of_two.dfy

method Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
  decreases x, y
{
  if x >= y {
    return x;
  } else {
    return y;
  }
}
