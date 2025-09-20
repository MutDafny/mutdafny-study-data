// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_PrecedenceLinter.dfy

predicate P0(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A &&
  B ==>
    C
}

predicate P1(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A &&
  B ==>
    C
}

predicate P2(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A &&
  B ==>
    C
}

predicate P3(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate P4(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate P5(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A ==>
    B &&
    C
}

predicate P6(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A ==>
    B || C
}

predicate Q0(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q1(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q2(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q3(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q4(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q4a(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q4b(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q4c(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q4d(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q5(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q6(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    C &&
    D
}

predicate Q7(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A ==>
    B &&
    C &&
    D
}

predicate Q8(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A ==>
    B &&
    C &&
    D
}

predicate Q8a(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  (A ==>
    B &&
    C &&
    D) &&
  (B || C)
}

predicate Q8b(A: bool, B: bool, C: bool, D: bool)
  decreases A, B, C, D
{
  A &&
  B ==>
    B &&
    D
}

predicate Q8c(t: int, x: int, y: int)
  decreases t, x, y
{
  (t == 2 ==>
    x < y) &&
  (t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000) &&
  (t == 4 ==>
    0 <= x || 0 <= y)
}

predicate Q8d(t: int, x: int, y: int)
  decreases t, x, y
{
  t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000
}

predicate Q9(A: bool, B: bool, C: bool)
  decreases A, B, C
{
  A ==>
    B ==>
      C
}

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    (P(x) ==>
      Q(x)) &&
    (P(x) ==>
      R(x))
}

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) &&
    Q(x) ==>
      R(x)
}

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger P(x)} :: 
    P(x) ==>
      forall y: int {:trigger Q(y)} :: 
        Q(y) ==>
          R(x)
}

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x: int {:trigger R(x)} {:trigger P(x)} :: 
    P(x) &&
    exists y: int {:trigger Q(y)} :: 
      Q(y) &&
      R(x)
}

lemma Injective()
  ensures forall x: int, y: int {:trigger Negate(y), Negate(x)} :: Negate(x) == Negate(y) ==> x == y
{
}

function Negate(x: int): int
  decreases x
{
  -x
}

predicate Quant0(s: string)
  decreases s
{
  s != [] &&
  ('a' <= s[0] <= 'z' || 'A' <= s[0] <= 'Z') &&
  forall i: int {:trigger s[i]} :: 
    1 <= i < |s| ==>
      'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z' || '0' <= s[i] <= '9'
}

predicate Quant1(m: array2<string>, P: int -> bool)
  reads m
  decreases {m}, m
{
  forall i: int {:trigger P(i)} :: 
    0 <= i < m.Length0 &&
    P(i) ==>
      forall j: int {:trigger m[i, j]} :: 
        0 <= j < m.Length1 ==>
          m[i, j] != ""
}

predicate Quant2(s: string)
  decreases s
{
  forall i: int {:trigger s[i]} :: 
    0 <= i < |s| ==>
      if s[i] == '*' then false else s[i] == 'a' || s[i] == 'b'
}

ghost predicate Quant3(f: int -> int, g: int -> int)
{
  forall x: int {:trigger g(x)} {:trigger f(x)} :: 
    f(x) == g(x)
}

ghost predicate Quant4(f: int -> int, g: int -> int)
{
  forall x: int {:trigger g(x)} {:trigger f(x)} :: 
    f(x) == g(x)
}

ghost predicate Quant5(f: int -> int, g: int -> int)
{
  forall x: int {:trigger g(x)} {:trigger f(x)} :: 
    f(x) == g(x)
}

function If0(s: string): int
  decreases s
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

function If1(s: string): int
  decreases s
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

function If2(s: string): int
  decreases s
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

function If3(s: string): int
  decreases s
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

predicate Waterfall(A: bool, B: bool, C: bool, D: bool, E: bool)
  decreases A, B, C, D, E
{
  A ==>
    B ==>
      C ==>
        D ==>
          E
}

ghost predicate MoreOps0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger P(x)} {:trigger Q(x)} {:trigger R(x)} :: 
    P(x) <==
      Q(x) <==
      R(x)
}

ghost predicate MoreOps1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger P(x)} {:trigger Q(x)} :: 
    P(x) <== Q(x) <==> R(x)
}

ghost predicate MoreOps2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) ==> Q(x) <==> R(x)
}

ghost predicate MoreOps3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) ==> Q(x) <==> R(x) ==> P(x)
}

ghost predicate MoreOps4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x: int {:trigger R(x)} {:trigger Q(x)} {:trigger P(x)} :: 
    P(x) <==> Q(x) && R(x)
}

lemma IntLemma(x: int)
  decreases x

function StmtExpr0(x: int): int
  decreases x
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}

function StmtExpr1(x: int): int
  decreases x
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}

function StmtExpr2(x: int): int
  decreases x
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}

function StmtExpr3(x: int): int
  decreases x
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}

function FunctionWithDefaultParameterValue(x: int, y: int := 100): int
  decreases x, y

function UseDefaultValues(x: int): int
  decreases x
{
  if x <= 0 then
    0
  else
    FunctionWithDefaultParameterValue(x - 1)
}

function Square(x: int): int
  decreases x
{
  x * x
}

predicate Let0(lo: int, hi: int)
  requires lo <= hi
  decreases lo, hi
{
  forall x: int {:trigger Square(x)} :: 
    lo <= x < hi ==>
      var square: int := Square(x); 0 <= square
}

ghost predicate Let1(P: int -> bool)
{
  forall x: int {:trigger P(x)} :: 
    0 <= x &&
    P(x) ==>
      ghost var bigger: int /*{:_delayTriggerWarning}*/ /*{:_noAutoTriggerFound}*/ :| x <= bigger; 0 <= bigger
}

predicate SomeProperty<X>(x: X)

method Parentheses0(arr: array<int>, P: int -> bool)
  decreases arr
{
  assert forall i: int {:trigger old(arr[i])} {:trigger arr[i]} :: 0 <= i < arr.Length ==> arr[i] == old(arr[i]);
  var x := forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length ==> SomeProperty(arr[i]);
  var y := forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length ==> P(arr[i]);
  assert forall i: int {:trigger SomeProperty(i)} :: 0 <= i < arr.Length && SomeProperty(i) ==> unchanged(arr);
  ghost var u := if arr.Length == 3 then true else fresh(arr);
}

method Parentheses1(w: bool, x: int)
  decreases w, x
{
  var a := if w then {} else {x, x, x};
  var b := if w then iset{} else iset{x, x, x};
  var c := if w then [] else [x, x, x];
  var d := if w then multiset{} else multiset{x, x, x};
  var e := if w then map[] else map[x := x];
  var f := if w then imap[] else imap[x := x];
}

method Parentheses2(w: bool, x: int, y: int)
  decreases w, x, y
{
  var a := if w then Record(0, 0) else Record(x, y);
  var b := if w then a else a.(x := y);
}

method Parentheses3(w: bool, arr: array<int>, m: array2<int>, i: nat, j: nat)
  requires i < j < arr.Length <= m.Length0 <= m.Length1
  decreases w, arr, m, i, j
{
  var a := if w then 0 else arr[i];
  var b := if w then [] else arr[i..];
  var c := if w then [] else arr[..i];
  var d := if w then [] else arr[i .. j];
  var e := if w then [] else arr[..j][i..];
  var f := if w then [] else arr[..i] + arr[i..];
  var g := if w then 0 else m[i, j];
  var h := if w then arr[..] else arr[..j][0 := 25];
}

method Parentheses4(w: bool, s: Stream, t: Stream)
  decreases w
{
  ghost var a := if w then true else s ==#[12] t;
  ghost var b := if w then true else s ==#[12] t;
  ghost var c := if w then true else s !=#[12] t;
  ghost var d := if w then true else s !=#[12] t;
}

datatype Record = Record(x: int, y: int)

codatatype Stream = More(head: int, tail: Stream)

module MyModule {
  function MyFunction(x: int): int
    decreases x

  lemma Lemma(x: int)
    decreases x
}

module QualifiedNames {
  predicate P(x: int)
    decreases x
  {
    var u: int := x;
    MyModule.MyFunction(x) == x
  }

  predicate Q(x: int)
    decreases x
  {
    var u: int := x;
    MyModule.Lemma(x);
    x == MyModule.MyFunction(x)
  }

  function F(): int
  {
    var p: int := 1000;
    MyModule.Lemma(p);
    p
  }

  predicate R(x: int)
    decreases x
  {
    !var u: int := x; MyModule.Lemma(x); x == MyModule.MyFunction(x)
  }

  import MyModule
}

module MatchAcrossMultipleLines {
  method M(s: set<PQ>)
    requires forall pq: PQ {:trigger pq in s} | pq in s :: match pq { case P(x) => true case Q(y) => y == false }
    decreases s
  {
  }

  function F(A: bool, B: int, C: YZ): int
    requires C != Y
    decreases A, B, C
  {
    if A then
      B
    else
      match C { case Z() => 3 }
  }

  datatype PQ = P(int) | Q(bool)

  datatype YZ = Y | Z
}
