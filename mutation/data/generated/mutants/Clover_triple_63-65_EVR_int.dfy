// Clover_triple.dfy

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
  decreases x
{
  r := 0;
}
