// Dafny-Exercises_tmp_tmpjm75muf__Session10Exercises_ExerciseBarrier.dfy

method barrier(v: array<int>, p: int) returns (b: bool)
  requires v.Length > 0
  requires 0 <= p < v.Length
  ensures b == forall k: int, l: int {:trigger v[l], v[k]} :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
  decreases v, p
{
  var i := 1;
  var max := 0;
  while i != p
    invariant 0 <= i <= p + 1
    invariant 0 <= max < i
    invariant forall k: int {:trigger v[k]} :: 0 <= k < i ==> v[max] >= v[k]
    decreases p - i
  {
    if v[i] > v[max] {
      max := i;
    }
    i := i + 1;
  }
  while i < v.Length && v[i] > v[max]
    invariant 0 <= i <= v.Length
    invariant forall k: int {:trigger v[k]} :: 0 <= k <= p ==> v[k] <= v[max]
    invariant forall k: int {:trigger v[k]} :: p < k < i ==> v[k] > v[max]
    decreases v.Length - i
  {
    i := i + 1;
  }
  b := i == v.Length;
}
