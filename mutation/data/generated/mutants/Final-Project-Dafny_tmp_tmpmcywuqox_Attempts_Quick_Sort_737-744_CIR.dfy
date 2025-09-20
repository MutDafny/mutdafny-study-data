// Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Quick_Sort.dfy

predicate quickSorted(Seq: seq<int>)
  decreases Seq
{
  forall idx_1: int, idx_2: int {:trigger Seq[idx_2], Seq[idx_1]} :: 
    0 <= idx_1 < idx_2 < |Seq| ==>
      Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres: int, Seq: seq<int>)
    returns (Seq_1: seq<int>, Seq_2: seq<int>)
  ensures (forall x: int {:trigger x in Seq_1} | x in Seq_1 :: x <= thres) && forall x: int {:trigger x in Seq_2} | x in Seq_2 :: x >= thres
  ensures |Seq_1| + |Seq_2| == |Seq|
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
  decreases thres, Seq
{
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  while i < |Seq|
    invariant i <= |Seq|
    invariant (forall x: int {:trigger x in Seq_1} | x in Seq_1 :: x <= thres) && forall x: int {:trigger x in Seq_2} | x in Seq_2 :: x >= thres
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq[..i]) == multiset(Seq_1) + multiset(Seq_2)
    decreases |Seq| - i
  {
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    assert Seq[..i] + [Seq[i]] == Seq[..i + 1];
    i := i + 1;
  }
  assert Seq[..|Seq|] == Seq;
}

lemma Lemma_1(Seq_1: seq, Seq_2: seq)
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x {:trigger x in Seq_2} {:trigger x in Seq_1} | x in Seq_1 :: x in Seq_2
  decreases Seq_1, Seq_2
{
  forall x | x in Seq_1
    ensures x in multiset(Seq_1)
  {
    ghost var i := 0;
    while i < |Seq_1|
      invariant 0 <= i <= |Seq_1|
      invariant forall idx_1: int {:trigger Seq_1[idx_1]} | 0 <= idx_1 < i :: Seq_1[idx_1] in multiset(Seq_1)
      decreases |Seq_1| - i
    {
      i := i + 1;
    }
  }
}

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
{
  if |Seq| == 0 {
    return [];
  } else if |Seq| == 1 {
    return Seq;
  } else {
    var Seq_1, Seq_2 := threshold(Seq[0], Seq[1..]);
    var Seq_1' := quickSort(Seq_1);
    Lemma_1(Seq_1', Seq_1);
    var Seq_2' := quickSort(Seq_2);
    Lemma_1(Seq_2', Seq_2);
    assert Seq == [Seq[0]] + Seq[1..];
    return Seq_1' + [Seq[0]] + Seq_2';
  }
}
