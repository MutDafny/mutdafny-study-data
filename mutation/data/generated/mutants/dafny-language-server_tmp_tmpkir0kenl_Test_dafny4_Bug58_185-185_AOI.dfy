// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug58.dfy

function M1(f: map<int, bool>, i: int): bool
  decreases f, i

function M2(f: map<int, bool>, i: int): bool
  decreases f, i
{
  M1(map j: int {:trigger j in f} | j in f :: f[-j], i)
}

lemma L(f: map<int, bool>, i: int)
  requires i in f
  requires M2(f, i)
  requires forall j: int, f: map<int, bool> {:trigger f[j]} {:trigger j in f} {:trigger M1(f, j)} :: M1(f, j) == (j in f && f[j])
  decreases f, i
{
  assert f[i];
}
