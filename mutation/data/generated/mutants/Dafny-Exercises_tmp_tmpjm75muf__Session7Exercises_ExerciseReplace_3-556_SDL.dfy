// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseReplace.dfy

method replace(v: array<int>, x: int, y: int)
  modifies v
  ensures forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < old(v.Length) && old(v[k]) == x ==> v[k] == y
  ensures forall k: int {:trigger v[k]} {:trigger old(v[k])} :: 0 <= k < old(v.Length) && old(v[k]) != x ==> v[k] == old(v[k])
  decreases v, x, y
{
}
