// dafny-workout_tmp_tmp0abkw6f8_starter_ex02.dfy

method Abs(x: int) returns (y: int)
  requires x < 0
  ensures 0 < y
  ensures y == -x
  decreases x
{
  return -x;
}

method Main()
{
  var a := Abs(3);
  assert a == 3;
}
