// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseSeparate.dfy

predicate strictNegative(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  reads v
  decreases {v}, v, i, j
{
  forall u: int {:trigger v[u]} | i <= u < j :: 
    v[u] < 0
}

predicate positive(s: seq<int>)
  decreases s
{
  forall u: int {:trigger s[u]} :: 
    0 <= u < |s| ==>
      s[u] >= 0
}

predicate isPermutation(s: seq<int>, t: seq<int>)
  decreases s, t
{
  multiset(s) == multiset(t)
}

method separate(v: array<int>) returns (i: int)
  modifies v
  ensures 0 <= i <= v.Length
  ensures positive(v[0 .. i]) && strictNegative(v, i, v.Length)
  ensures isPermutation(v[0 .. v.Length], old(v[0 .. v.Length]))
  decreases v
{
  i := 0;
  var j := v.Length - 1;
  while i <= j
    invariant 0 <= i <= j + 1 <= v.Length
    invariant strictNegative(v, j + 1, v.Length)
    invariant positive(v[0 .. i])
    invariant isPermutation(v[0 .. v.Length], old(v[0 .. v.Length]))
    decreases j - i
  {
    if v[i] >= 0 {
      i := j + 1;
    } else if v[j] >= 0 {
      assert v[i] < 0;
      v[i], v[j] := v[j], v[i];
      j := j - 1;
      i := i + 1;
    } else if v[j] < 0 {
      j := j - 1;
    }
  }
}
