// dafny-synthesis_task_id_557.dfy

predicate IsLowerCase(c: char)
  decreases c
{
  97 <= c as int <= 122
}

predicate IsUpperCase(c: char)
  decreases c
{
  65 <= c as int <= 90
}

predicate IsLowerUpperPair(c: char, C: char)
  decreases c, C
{
  c as int == C as int + 32
}

predicate IsUpperLowerPair(C: char, c: char)
  decreases C, c
{
  C as int == c as int - 32
}

function ShiftMinus32(c: char): char
  decreases c
{
  ((c as int - 32) % 128) as char
}

function Shift32(c: char): char
  decreases c
{
  ((c as int + 32) % 128) as char
}

method ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i: int {:trigger v[i]} {:trigger s[i]} :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
  decreases s
{
  var s': string := [];
  for i: int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k: int {:trigger s'[k]} {:trigger s[k]} :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    if IsLowerCase(s[i]) {
      s' := s + [ShiftMinus32(s[i])];
    } else if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}
