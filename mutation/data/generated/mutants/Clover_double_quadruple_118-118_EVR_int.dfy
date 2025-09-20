// Clover_double_quadruple.dfy

method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
  decreases x
{
  a := 2 * x;
  b := 2 * 0;
}
