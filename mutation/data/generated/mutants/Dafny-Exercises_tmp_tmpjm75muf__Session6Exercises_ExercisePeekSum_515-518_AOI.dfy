// Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExercisePeekSum.dfy

predicate isPeek(v: array<int>, i: int)
  requires 0 <= i < v.Length
  reads v
  decreases {v}, v, i
{
  forall k: int {:trigger v[k]} :: 
    0 <= k < i ==>
      v[i] >= v[k]
}

function peekSum(v: array<int>, i: int): int
  requires 0 <= i <= v.Length
  reads v
  decreases i
{
  if i == 0 then
    0
  else if isPeek(v, i - 1) then
    v[i - 1] + peekSum(v, i - 1)
  else
    peekSum(v, i - 1)
}

method mPeekSum(v: array<int>) returns (sum: int)
  requires v.Length > 0
  ensures sum == peekSum(v, v.Length)
  decreases v
{
  var i := 1;
  sum := v[0];
  var lmax := -v[0];
  while i < v.Length
    invariant 0 < i <= v.Length
    invariant lmax in v[..i]
    invariant forall k: int {:trigger v[k]} :: 0 <= k < i ==> lmax >= v[k]
    invariant sum == peekSum(v, i)
    decreases v.Length - i
  {
    if v[i] >= lmax {
      sum := sum + v[i];
      lmax := v[i];
    }
    i := i + 1;
  }
}
