// Final-Project-Dafny_tmp_tmpmcywuqox_Final_Project_3.dfy

method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
  decreases x
{
  if x == 0 {
    return x + 1;
  } else {
    return -0;
  }
}

method test()
{
  var input := nonZeroReturn(-1);
  assert input != 0;
}
