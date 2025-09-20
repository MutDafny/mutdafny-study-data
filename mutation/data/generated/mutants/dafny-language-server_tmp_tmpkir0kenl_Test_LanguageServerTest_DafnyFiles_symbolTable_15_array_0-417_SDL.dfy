// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method Main()
{
}

method foo(s: seq<int>)
  requires |s| > 1
  decreases s
{
  print s[1];
}
