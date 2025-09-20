// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue133.dfy

lemma Test(s: State)
  requires 42 in s.m
  ensures s.(m := s.m[42 := s.m[42]]) == s
  decreases s
{
  ghost var s' := s.(m := s.m[42 := s.m[42]]);
  assert s'.m == s.m;
}

lemma AnotherTest(a: MyDt, b: MyDt, c: bool)
  requires a.MakeB? && b.MakeB?
  requires a.s == multiset(a.t.m.Keys) && |b.s| == 0
  requires a.t.m == map[] && |b.t.m| == 0
  decreases a, b, c
{
  assert a == b;
}

method ChangeGen(g: GenDt)
  decreases g
{
  match g
  case {:split false} Left(_ /* _v5 */) =>
  case {:split false} Right(u) =>
    var h := g.(y := u);
    assert g == h;
}

lemma RecLem(r: Recursive) returns (s: Recursive)
  ensures r == s
  decreases r
{
  match r
  case {:split false} Red() =>
    s := Red;
  case {:split false} Green(next, m) =>
    ghost var n := RecLem(next);
    s := Green(n, m + m);
}

datatype State = State(m: map<int, bool>)

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)

datatype GenDt<X, Y> = Left(X) | Middle(X, int, Y) | Right(y: Y)

datatype Recursive<X> = Red | Green(next: Recursive<X>, m: set<X>)
