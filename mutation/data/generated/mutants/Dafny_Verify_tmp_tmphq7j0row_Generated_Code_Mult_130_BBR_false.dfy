// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
  decreases a, b
{
  x := 0;
  var y := a;
  while false
    invariant x == (a - y) * b
  {
    x := x + b;
    y := y - 1;
  }
}
