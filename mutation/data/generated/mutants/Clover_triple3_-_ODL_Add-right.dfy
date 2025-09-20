// Clover_triple3.dfy

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
  decreases x
{
  if x == 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x;
  }
}
