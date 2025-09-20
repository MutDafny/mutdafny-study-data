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
}
