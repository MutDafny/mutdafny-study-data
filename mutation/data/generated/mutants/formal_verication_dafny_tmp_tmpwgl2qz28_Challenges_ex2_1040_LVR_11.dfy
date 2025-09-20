// formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex2.dfy

method Forbid42(x: int, y: int) returns (z: int)
  requires y != 42
  ensures z == x / (42 - y)
  decreases x, y
{
  z := x / (42 - y);
  return z;
}

method Allow42(x: int, y: int)
    returns (z: int, err: bool)
  ensures y != 42 ==> z == x / (42 - y) && err == false
  ensures y == 42 ==> z == 0 && err == true
  decreases x, y
{
  if y != 42 {
    z := x / (42 - y);
    return z, false;
  }
  return 0, true;
}

method TEST1()
{
  var c: int := Forbid42(0, 1);
  assert c == 0;
  c := Forbid42(11, 32);
  assert c == 1;
  c := Forbid42(-100, 38);
  assert c == -25;
  var d: int, z: bool := Allow42(0, 42);
  assert d == 0 && z == true;
  d, z := Allow42(-10, 42);
  assert d == 0 && z == true;
  d, z := Allow42(0, 1);
  assert d == 0 && z == false;
  d, z := Allow42(10, 32);
  assert d == 1 && z == false;
  d, z := Allow42(-100, 38);
  assert d == -25 && z == false;
}
