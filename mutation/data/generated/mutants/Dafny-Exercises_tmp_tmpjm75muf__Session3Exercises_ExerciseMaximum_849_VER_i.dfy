// Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum.dfy

method mmaximum1(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> v[i] >= v[k]
  decreases v
{
  var j := 1;
  i := 0;
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k: int {:trigger v[k]} :: 0 <= k < j ==> v[i] >= v[k]
    decreases v.Length - j
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
}

method mmaximum2(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> v[i] >= v[k]
  decreases v
{
  var j := v.Length - 2;
  i := v.Length - 1;
  while j >= 0
    invariant 0 <= i < v.Length
    invariant -1 <= j < v.Length - 1
    invariant forall k: int {:trigger v[k]} :: v.Length > k > j ==> v[k] <= v[i]
    decreases j
  {
    if v[i] > v[i] {
      i := j;
    }
    j := j - 1;
  }
}

method mfirstMaximum(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l: int {:trigger v[l]} :: 0 <= l < i ==> v[i] > v[l]
  decreases v
{
  var j := 1;
  i := 0;
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k: int {:trigger v[k]} :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall k: int {:trigger v[k]} :: 0 <= k < i ==> v[i] > v[k]
    decreases v.Length - j
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
}

method mlastMaximum(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l: int {:trigger v[l]} :: i < l < v.Length ==> v[i] > v[l]
  decreases v
{
  var j := v.Length - 2;
  i := v.Length - 1;
  while j >= 0
    invariant -1 <= j < v.Length - 1
    invariant 0 <= i < v.Length
    invariant forall k: int {:trigger v[k]} :: v.Length > k > j ==> v[k] <= v[i]
    invariant forall k: int {:trigger v[k]} :: v.Length > k > i ==> v[k] < v[i]
    decreases j
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j - 1;
  }
}

method mmaxvalue1(v: array<int>) returns (m: int)
  requires v.Length > 0
  ensures m in v[..]
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> m >= v[k]
  decreases v
{
  var i := mmaximum1(v);
  m := v[i];
}

method mmaxvalue2(v: array<int>) returns (m: int)
  requires v.Length > 0
  ensures m in v[..]
  ensures forall k: int {:trigger v[k]} :: 0 <= k < v.Length ==> m >= v[k]
  decreases v
{
  var i := mmaximum2(v);
  m := v[i];
}
