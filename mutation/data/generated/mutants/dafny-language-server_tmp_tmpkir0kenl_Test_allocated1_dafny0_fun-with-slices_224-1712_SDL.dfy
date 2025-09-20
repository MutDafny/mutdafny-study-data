// dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices.dfy

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
  decreases s, a, index
{
}
