// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Regression19.dfy

predicate ContainsNothingBut5(s: set<int>)
  decreases s
{
  forall q: int {:trigger q in s} :: 
    q in s ==>
      q == 5
}

predicate YeahContains5(s: set<int>)
  decreases s
{
  exists q: int {:trigger q in s} :: 
    q in s &&
    q == 5
}

predicate ViaSetComprehension(s: set<int>)
  decreases s
{
  |set q: int {:trigger q in s} | q in s && q == 5| != 0
}

predicate LambdaTest(s: set<int>)
  decreases s
{
  ((q: int) => q in s)(5)
}

predicate ViaMapComprehension(s: set<int>)
  decreases s
{
  |(map q: int {:trigger q in s} | q in s && q == 5 :: true).Keys| != 0
}

predicate Contains5(s: set<int>)
  decreases s
{
  var q: int := 5;
  q in s
}

predicate RIs5(r: R)
  decreases r
{
  match r
  case MakeR(q) =>
    q == 5
  case Other() =>
    false
}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
  decreases x, s
{
}

lemma NonemptyMap(x: int, s: map<int, bool>)
  requires x in s.Keys
  ensures |s| != 0
  decreases x, s
{
}

method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
  decreases s, r, q
{
  assert ContainsNothingBut5(s);
  assert YeahContains5(s);
  NonemptySet(5, set q: int {:trigger q in s} | q in s && q == 5);
  assert ViaSetComprehension(s);
  NonemptyMap(5, map q: int {:trigger q in s} | q in s && -q == 5 :: true);
  assert ViaMapComprehension(s);
  assert LambdaTest(s);
  assert Contains5(s);
  assert RIs5(r);
}

datatype R = MakeR(int) | Other
