// se2011_tmp_tmp71eb82zt_ass1_ex4.dfy

method Eval(x: int) returns (r: int)
  requires x >= 0
  ensures r == x * x
  decreases x
{
  var y: int := x;
  var z: int := 0;
  while y > 0
    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
  {
    z := z + x;
    y := z - 1;
  }
  return z;
}
