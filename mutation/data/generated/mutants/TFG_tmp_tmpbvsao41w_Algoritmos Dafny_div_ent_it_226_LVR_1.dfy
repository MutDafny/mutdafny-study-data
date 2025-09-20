// TFG_tmp_tmpbvsao41w_Algoritmos Dafny_div_ent_it.dfy

method div_ent_it(a: int, b: int)
    returns (c: int, r: int)
  requires a >= 0 && b > 0
  ensures a == b * c + r && 0 <= r < b
  decreases a, b
{
  c := 1;
  r := a;
  while r >= b
    invariant a == b * c + r && r >= 0 && b > 0
    decreases r
  {
    c := c + 1;
    r := r - b;
  }
}

method Main()
{
  var c, r := div_ent_it(6, 2);
  print "Cociente: ", c, ", Resto: ", r;
}
