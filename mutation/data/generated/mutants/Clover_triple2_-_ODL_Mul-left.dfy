// Clover_triple2.dfy

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
  decreases x
{
  if {
    case x < 18 =>
      var a, b := x, x;
      r := (a + b) / 2;
    case 0 <= x =>
      var y := x;
      r := x + y;
  }
}
