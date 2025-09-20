// Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExerciseCountEven.dfy

predicate positive(s: seq<int>)
  decreases s
{
  forall u: int {:trigger s[u]} :: 
    0 <= u < |s| ==>
      s[u] >= 0
}

predicate isEven(i: int)
  requires i >= 0
  decreases i
{
  i - 2 == 0
}

function CountEven(s: seq<int>): int
  requires positive(s)
  decreases s
{
  if s == [] then
    0
  else
    (if s[|s| - 1] % 2 == 0 then 1 else 0) + CountEven(s[..|s| - 1])
}

lemma ArrayFacts<T>()
  ensures forall v: array<T> {:trigger v[..]} {:trigger v.Length} :: v[..v.Length] == v[..]
  ensures forall v: array<T> {:trigger v[..]} {:trigger v[0..]} :: v[0..] == v[..]
  ensures forall v: array<T> {:trigger v[..]} {:trigger v.Length} :: v[0 .. v.Length] == v[..]
  ensures forall v: array<T> {:trigger v.Length} :: |v[0 .. v.Length]| == v.Length
  ensures forall v: array<T> {:trigger v.Length} | v.Length >= 1 :: |v[1 .. v.Length]| == v.Length - 1
  ensures forall v: array<T> {:trigger v.Length} :: forall k: nat, _t#0: int {:trigger v[..k], v[.._t#0]} | _t#0 == k + 1 && k < v.Length :: v[.._t#0][..k] == v[..k]
{
}

method mcountEven(v: array<int>) returns (n: int)
  requires positive(v[..])
  ensures n == CountEven(v[..])
  decreases v
{
  ArrayFacts<int>();
  n := 0;
  var i: int;
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant n == CountEven(v[..i])
    decreases v.Length - i
  {
    if v[i] % 2 == 0 {
      n := n + 1;
    }
    i := i + 1;
  }
}
