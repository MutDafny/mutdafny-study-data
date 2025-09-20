// Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems.dfy

function SumR(s: seq<int>): int
  decreases s
{
  if s == [] then
    0
  else
    SumR(s[..|s| - 1]) + s[|s| - 1]
}

function SumL(s: seq<int>): int
  decreases s
{
  if s == [] then
    0
  else
    s[0] + SumL(s[1..])
}

lemma concatLast(s: seq<int>, t: seq<int>)
  requires t != []
  ensures (s + t)[..|s + t| - 1] == s + t[..|t| - 1]
  decreases s, t
{
}

lemma concatFirst(s: seq<int>, t: seq<int>)
  requires s != []
  ensures (s + t)[1..] == s[1..] + t
  decreases s, t
{
}

lemma {:induction s, t} /*{:_inductionTrigger s + t}*/ /*{:_induction s, t}*/ SumByPartsR(s: seq<int>, t: seq<int>)
  ensures SumR(s + t) == SumR(s) + SumR(t)
  decreases s, t
{
  if t == [] {
    assert s + t == s;
  } else if s == [] {
    assert s + t == t;
  } else {
    calc == {
      SumR(s + t);
      SumR((s + t)[..|s + t| - 1]) + (s + t)[|s + t| - 1];
      SumR((s + t)[..|s + t| - 1]) + t[|t| - 1];
      {
        concatLast(s, t);
      }
      SumR(s + t[..|t| - 1]) + t[|t| - 1];
      {
        SumByPartsR(s, t[..|t| - 1]);
      }
      SumR(s) + SumR(t[..|t| - 1]) + t[|t| - 1];
      SumR(s) + SumR(t);
    }
  }
}

lemma {:induction s, t} /*{:_inductionTrigger s + t}*/ /*{:_induction s, t}*/ SumByPartsL(s: seq<int>, t: seq<int>)
  ensures SumL(s + t) == SumL(s) + SumL(t)
  decreases s, t
{
  if t == [] {
    assert s + t == s;
  } else if s == [] {
    assert s + t == t;
  } else {
    calc == {
      SumL(s + t);
      (s + t)[0] + SumL((s + t)[1..]);
      s[0] + SumL((s + t)[1..]);
      {
        concatFirst(s, t);
      }
      s[0] + SumL(s[1..] + t);
      {
        SumByPartsL(s[1..], t);
      }
      s[0] + SumL(s[1..]) + SumL(t);
    }
  }
}

lemma {:induction s, i, j} /*{:_inductionTrigger s[i .. j]}*/ /*{:_induction s, i, j}*/ equalSumR(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures SumR(s[i .. j]) == SumL(s[i .. j])
  decreases j - i
{
  if s == [] {
    assert SumR(s) == SumL(s);
  } else {
    if i == j {
      assert SumR(s[i .. j]) == SumL(s[i .. j]);
    } else {
      calc == {
        SumR(s[i .. j]);
        {
          assert s[i .. j] == s[i .. j - 1] + [s[j - 1]];
          assert SumR(s[i .. j]) == SumR(s[i .. j - 1]) + s[j - 1];
        }
        SumR(s[i .. j - 1]) + s[j - 1];
        {
          equalSumR(s, i, j - 1);
        }
        SumL(s[i .. j - 1]) + s[j - 1];
        {
          assert s[j - 1] == SumL([s[j - 1]]);
        }
        SumL(s[i .. j - 1]) + SumL([s[j - 1]]);
        {
          SumByPartsL(s[i .. j - 1], [s[j - 1]]);
        }
        SumL(s[i .. j - 1] + [s[j - 1]]);
        {
          assert s[i .. j] == s[i .. j - 1] + [s[j - 1]];
        }
        SumL(s[i .. j]);
      }
    }
  }
}

lemma equalSumsV()
  ensures forall j: int, i: int, v: array<int> {:trigger v[i .. j]} | 0 <= i <= j <= v.Length :: SumR(v[i .. j]) == SumL(v[i .. j])
{
  forall v: array<int>, i: int, j: int | 0 <= i <= j <= v.Length
    ensures SumR(v[i .. j]) == SumL(v[i .. j])
  {
    equalSumR(v[..], i, j);
  }
}

function SumV(v: array<int>, c: int, f: int): int
  requires 0 <= c <= f <= v.Length
  reads v
  decreases {v}, v, c, f
{
  SumR(v[c .. f])
}

lemma ArrayFacts<T>()
  ensures forall v: array<T> {:trigger v[..]} {:trigger v.Length} :: v[..v.Length] == v[..]
  ensures forall v: array<T> {:trigger v[..]} {:trigger v[0..]} :: v[0..] == v[..]
  ensures forall v: array<T> {:trigger v[..]} {:trigger v.Length} :: v[0 .. v.Length] == v[..]
  ensures forall v: array<T> {:trigger v.Length} :: |v[0 .. v.Length]| == v.Length
  ensures forall v: array<T> {:trigger v.Length} | v.Length >= 1 :: |v[1 .. v.Length]| == v.Length - 1
  ensures forall v: array<T> {:trigger v.Length} :: forall k: nat, _t#0: int {:trigger v[..k], v[.._t#0]} | _t#0 == k + 1 && k < v.Length :: v[.._t#0][..k] == v[..k]
{
  equalSumsV();
}

method sumElems(v: array<int>) returns (sum: int)
  ensures sum == SumR(v[..])
  decreases v
{
  ArrayFacts<int>();
  sum := 0;
  var i: int;
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length && sum == SumR(v[..i])
    decreases v.Length - i
  {
    sum := sum + v[i];
    i := i + 1;
  }
}

method sumElemsB(v: array<int>) returns (sum: int)
  ensures sum == SumR(v[0 .. v.Length])
  decreases v
{
  ArrayFacts<int>();
  sum := 0;
  var i: int;
  i := v.Length;
  equalSumsV();
  while i != 0
    invariant 0 <= i <= v.Length
    invariant sum == SumL(v[i..]) == SumR(v[i..])
    decreases i
  {
    sum := sum + v[i - 1];
    i := i - 1;
  }
}
