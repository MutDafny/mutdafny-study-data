// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExercisePositive.dfy

predicate positive(s: seq<int>)
  decreases s
{
  forall u: int {:trigger s[u]} :: 
    0 <= u < |s| ==>
      s[u] >= 0
}

method mpositive(v: array<int>) returns (b: bool)
  ensures b == positive(v[0 .. v.Length])
  decreases v
{
  var i := 0;
  while i < v.Length && v[i] >= 0
    invariant 0 <= i <= v.Length
    invariant positive(v[..i])
    decreases v.Length - i
  {
    i := i + 1;
  }
  b := i == v.Length;
}

method mpositive3(v: array<int>) returns (b: bool)
  ensures b == positive(v[0 .. v.Length])
  decreases v
{
  var i := 0;
  b := true;
  while i < v.Length && b
    invariant 0 <= i <= v.Length
    invariant b == positive(v[0 .. i])
    invariant !b ==> !positive(v[0 .. v.Length])
    decreases v.Length - i
  {
    b := v[i] >= 0;
    i := i + 1;
  }
}

method mpositive4(v: array<int>) returns (b: bool)
  ensures b == positive(v[0 .. v.Length])
  decreases v
{
  var i := 0;
  b := true;
  while i < v.Length && b
    invariant 0 <= i <= v.Length
    invariant b == positive(v[0 .. i])
    invariant !b ==> !positive(v[0 .. v.Length])
    decreases v.Length - i
  {
    b := v[i] >= 0;
    i := i + 1;
  }
}

method mpositivertl(v: array<int>) returns (b: bool)
  ensures b == positive(v[0 .. v.Length])
  decreases v
{
  var i := v.Length - 1;
  while i >= 0 && true
    invariant -1 <= i < v.Length
    invariant positive(v[i + 1..])
    decreases i
  {
    i := i - 1;
  }
  b := i == -1;
}
