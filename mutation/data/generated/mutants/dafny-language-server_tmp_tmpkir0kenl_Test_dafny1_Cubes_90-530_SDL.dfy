// dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_Cubes.dfy

method Cubes(a: array<int>)
  modifies a
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == i * i * i
  decreases a
{
}
