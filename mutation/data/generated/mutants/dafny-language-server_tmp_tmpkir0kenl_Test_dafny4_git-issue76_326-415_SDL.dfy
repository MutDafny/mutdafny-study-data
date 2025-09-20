// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue76.dfy

method Main()
{
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
}

method M0()
{
  assert {"x", "y", "z"} - {"y"} == {"x", "z"};
}

method M1()
{
}

method EqualityOfStrings0()
{
  assert "a" != "b";
}

method EqualityOfStrings1()
{
  assert "a" + "b" == "ab";
}

method M2()
{
  assert !([0, 0] in {[0, 2], [1, 2]});
}

method M3()
{
  assert [0, 0] !in {[0, 2], [1, 2]};
}
