// Clover_double_quadruple.dfy

method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
  decreases x
{
  b := 2 * a;
  a := 2 * x;
}
