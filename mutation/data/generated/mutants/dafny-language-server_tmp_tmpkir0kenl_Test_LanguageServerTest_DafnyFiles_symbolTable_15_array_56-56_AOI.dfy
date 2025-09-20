// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method Main()
{
  var i := 2;
  var s := [1, i, 3, 4, -5];
  print |s|;
  assert s[|s| - 1] == 5;
  assert s[|s| - 1 .. |s|] == [5];
  assert s[1..] == [2, 3, 4, 5];
  assert s[..|s| - 1] == [1, 2, 3, 4];
  assert s == s[0..] == s[..|s|] == s[0 .. |s|] == s[..];
}

method foo(s: seq<int>)
  requires |s| > 1
  decreases s
{
  print s[1];
}
