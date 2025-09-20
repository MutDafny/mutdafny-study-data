// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseReplace.dfy

method replace(v: array<int>, x: int, y: int)
  modifies v
  ensures forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < old(v.Length) && old(v[k]) == x ==> v[k] == y
  ensures forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < old(v.Length) && old(v[k]) != x ==> v[k] == old(v[k])
  decreases v, x, y
{
  var i := 0;
  while i <= v.Length
    invariant 0 <= i <= v.Length
    invariant forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < i && old(v[k]) == x ==> v[k] == y
    invariant forall k: int {:trigger old(v[k])} {:trigger v[k]} :: i <= k < v.Length ==> v[k] == old(v[k])
    invariant forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < i && old(v[k]) != x ==> v[k] == old(v[k])
    decreases v.Length - i
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
