// groupTheory_tmp_tmppmmxvu8h_tutorial2.dfy

ghost method M1()
{
  assert 1 != 3;
  assume 1 == 2;
  assert 1 == 2;
}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
  requires C == A * B
  ensures C <= A && C <= B
  decreases A, B, C
{
}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
  requires C == A + B
  ensures A <= C && B <= C
  decreases A, B, C
{
}

const s0 := {3, 8, 0}

lemma M2()
{
  ghost var s1 := {2, 4, 6, 8};
  assert |s1| == 4;
  s1 := {};
  assert |s1| == 0;
  assert s1 <= s0;
}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
  requires A == {}
  ensures A <= B
  decreases A, B
{
}

lemma AnySetIsASubsetOfItself(A: set)
  ensures A <= A
  decreases A
{
}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
  requires C == A * B && D == A + B
  ensures C <= D
  decreases A, B, C, D
{
  assert C <= A by {
    assert C == A * B;
    IntersectionIsSubsetOfBoth(A, B, C);
  }
  assert A <= D by {
    assert D == A + B;
    BothSetsAreSubsetsOfTheirUnion(A, B, D);
  }
}
