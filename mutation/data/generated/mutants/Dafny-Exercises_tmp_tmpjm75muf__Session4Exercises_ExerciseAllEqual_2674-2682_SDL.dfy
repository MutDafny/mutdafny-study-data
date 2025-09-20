// Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExerciseAllEqual.dfy

predicate allEqual(s: seq<int>)
  decreases s
{
  forall i: int, j: int {:trigger s[j], s[i]} :: 
    0 <= i < |s| &&
    0 <= j < |s| ==>
      s[i] == s[j]
}

lemma equivalenceNoOrder(s: seq<int>)
  ensures allEqual(s) <==> forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i <= j < |s| ==> s[i] == s[j]
  decreases s
{
}

lemma equivalenceEqualtoFirst(s: seq<int>)
  requires s != []
  ensures allEqual(s) <==> forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[0] == s[i]
  decreases s
{
}

lemma equivalenceContiguous(s: seq<int>)
  ensures allEqual(s) ==> forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == i + 1 :: 0 <= i && i < |s| - 1 ==> s[i] == s[_t#0]
  ensures allEqual(s) <== forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == i + 1 :: 0 <= i && i < |s| - 1 ==> s[i] == s[_t#0]
  decreases s
{
  assert allEqual(s) ==> forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == i + 1 :: 0 <= i && i < |s| - 1 ==> s[i] == s[_t#0];
  if |s| == 0 || |s| == 1 {
  } else {
    calc {
      forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == i + 1 :: 
        0 <= i &&
        i < |s| - 1 ==>
          s[i] == s[_t#0];
    ==>
      {
        equivalenceContiguous(s[..|s| - 1]);
        assert s[|s| - 2] == s[|s| - 1];
      }
      allEqual(s);
    }
  }
}

method mallEqual1(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0 .. v.Length])
  decreases v
{
  var i := 0;
  b := true;
  while i < v.Length && b
    invariant 0 <= i <= v.Length
    invariant b == allEqual(v[..i])
    decreases v.Length - i
  {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual2(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0 .. v.Length])
  decreases v
{
  var i: int;
  b := true;
  i := 0;
  while i < v.Length && v[i] == v[0]
    invariant 0 <= i <= v.Length
    invariant forall k: int {:trigger v[k]} :: 0 <= k < i ==> v[k] == v[0]
    decreases v.Length - i
  {
    i := i + 1;
  }
  b := i == v.Length;
}

method mallEqual3(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0 .. v.Length])
  decreases v
{
  equivalenceContiguous(v[..]);
  var i: int;
  b := true;
  if v.Length > 0 {
    i := 0;
    while i < v.Length - 1 && v[i] == v[i + 1]
      invariant 0 <= i <= v.Length - 1
      invariant b == allEqual(v[..i + 1])
      decreases v.Length - i
    {
      i := i + 1;
    }
    b := i == v.Length - 1;
  }
}

method mallEqual4(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0 .. v.Length])
  decreases v
{
  var i: int;
  b := true;
  if v.Length > 0 {
    i := 0;
    while i < v.Length - 1 && b
      invariant 0 <= i < v.Length
      invariant b == allEqual(v[..i + 1])
      decreases v.Length - i
    {
      b := v[i] == v[i + 1];
      i := i + 1;
    }
  }
}

method mallEqual5(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0 .. v.Length])
  decreases v
{
  var i := 0;
  b := true;
  while i < v.Length && b
    invariant 0 <= i <= v.Length
    invariant b ==> forall k: int {:trigger v[k]} :: 0 <= k < i ==> v[k] == v[0]
    invariant !b ==> exists k: int {:trigger v[k]} :: 0 <= k < v.Length && v[k] != v[0]
    decreases v.Length - i - if b then 0 else 1
  {
    if v[i] != v[0] {
      b := false;
    } else {
    }
  }
}
