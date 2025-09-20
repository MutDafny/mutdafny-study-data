// Formal-Methods-Project_tmp_tmphh2ar2xv_Factorial.dfy

method Fact(x: int) returns (y: int)
  requires x >= 0
  decreases x
{
  var z := 0;
  y := 1;
  while z != x
    invariant 0 <= x - z
    decreases x - z
  {
    z := z + 1;
    y := y * z;
  }
}

method Main()
{
  var a := Fact(87);
  print a;
}
