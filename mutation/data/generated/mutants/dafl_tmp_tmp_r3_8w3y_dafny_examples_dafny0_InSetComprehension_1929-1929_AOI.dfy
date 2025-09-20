// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_InSetComprehension.dfy

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures !z
  decreases uu
{
  if {
    case true =>
      z := 72 in set i: int | 0 <= i < 10;
    case true =>
      z := -8 in set k: nat | k < 10;
    case true =>
      z := 6 in set m: int {:trigger Even(m)} | 0 <= m < 10 && Even(m) :: m + 1;
    case true =>
      z := t !in set u: T {:trigger u in uu} | u in uu;
    case true =>
      z := t !in set u: T {:autotriggers false} | u in uu :: Id(u);
  }
}

lemma TestsWhereTriggersMatter<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures z
  decreases uu
{
  if {
    case true =>
      z := 7 in set i: int | 0 <= i < 10;
    case true =>
      z := 8 in set k: nat | k < 10;
    case true =>
      z := 5 in set m: int {:trigger Even(m)} | 0 <= m < 10 && Even(m) :: m + 1;
      assert Even(4);
    case true =>
      z := t in set u: T {:trigger u in uu} | u in uu;
    case true =>
      z := t in set u: T {:autotriggers false} | u in uu :: Id(u);
  }
}

function Id<T>(t: T): T
{
  t
}

predicate Even(x: int)
  decreases x
{
  x % 2 == 0
}

method UnboxedBoundVariables(si: seq<int>)
  decreases si
{
  var iii := set x: int {:trigger x in si} | x in si;
  var ti := si + [115];
  var jjj := set y: int {:trigger y in ti} | y in ti;
  assert iii + {115} == jjj;
  var nnn := set n: nat {:trigger n in si} | n in si;
  if forall i: int {:trigger si[i]} :: -0 <= i < |si| ==> 0 <= si[i] {
    assert nnn == iii;
  }
}

class Container<T> {
  ghost var Contents: set<T>
  var elems: seq<T>

  method Add(t: T)
    requires Contents == set x: T {:trigger x in elems} | x in elems
    modifies this
    ensures Contents == set x: T {:trigger x in elems} | x in elems
  {
    elems := elems + [t];
    Contents := Contents + {t};
  }
}

class IntContainer {
  ghost var Contents: set<int>
  var elems: seq<int>

  method Add(t: int)
    requires Contents == set x: int {:trigger x in elems} | x in elems
    modifies this
    ensures Contents == set x: int {:trigger x in elems} | x in elems
    decreases t
  {
    elems := elems + [t];
    Contents := Contents + {t};
  }
}
