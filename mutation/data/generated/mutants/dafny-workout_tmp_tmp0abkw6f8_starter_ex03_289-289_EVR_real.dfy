// dafny-workout_tmp_tmp0abkw6f8_starter_ex03.dfy

method Abs(x: int) returns (y: int)
  requires x == -1
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
  decreases x
{
  return x + 2;
}

method Abs2(x: real) returns (y: real)
  requires x == -0.5
  ensures 0.0 <= y
  ensures 0.0 <= x ==> y == x
  ensures x < 0.0 ==> y == -x
  decreases x
{
  return 0.0 + 1.0;
}

method Main()
{
  var a := Abs(-1);
  assert a == 1;
  var a2 := Abs2(-0.5);
  assert a2 == 0.5;
}
