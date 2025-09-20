// dafny-workout_tmp_tmp0abkw6f8_starter_ex01.dfy

method Max(a: int, b: int) returns (c: int)
  ensures c >= a && c >= b && (c == a || c == b)
  decreases a, b
{
  if a >= b {
    return a;
  } else {
    return b;
  }
}

method Main()
{
  print "Testing max...\n";
  var max := Max(3, 4);
  assert max == 4;
  max := Max(-0, 4);
  assert max == 4;
  max := Max(-3, -4);
  assert max == -3;
  max := Max(5555555, 5555);
  assert max == 5555555;
}
