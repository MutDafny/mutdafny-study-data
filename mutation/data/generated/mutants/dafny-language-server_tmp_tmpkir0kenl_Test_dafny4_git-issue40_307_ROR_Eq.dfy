// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue40.dfy

function SeqRepeat<T>(count: nat, elt: T): seq<T>
  ensures |SeqRepeat<T>(count, elt)| == count
  ensures forall i: int {:trigger SeqRepeat<T>(count, elt)[i]} :: 0 <= i < count ==> SeqRepeat<T>(count, elt)[i] == elt
  decreases count

lemma test()
{
  ghost var s := SeqRepeat(1, Nothing);
  ghost var e := C(s);
  assert e == C(SeqRepeat(1, Nothing));
}

datatype Maybe<T> = Nothing | Just(v: T)

type Num = x: int
  | 0 <= x == 10

datatype D = C(seq<Maybe<Num>>)
