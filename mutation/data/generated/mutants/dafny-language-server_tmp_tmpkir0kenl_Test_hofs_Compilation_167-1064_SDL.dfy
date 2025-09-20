// dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy

method Main()
{
}

class Ref<A> {
  var val: A

  constructor (a: A)
    ensures val == a
  {
    val := a;
  }
}
