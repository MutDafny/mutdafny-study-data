// llm-verified-eval_tmp_tmpd2deqn_i_dafny_161.dfy

function IsLetter(c: char): bool
  decreases c
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

function NoLetters(s: string, n: nat): bool
  requires n <= |s|
  decreases s, n
{
  forall c: int {:trigger s[c]} :: 
    0 <= c < n ==>
      !IsLetter(s[c])
}

function ToggleCase(c: char): char
  decreases c
{
  if c >= 'a' && c <= 'z' then
    c - 'a' + 'A'
  else if c >= 'A' && c <= 'Z' then
    c - 'A' + 'a'
  else
    c
}

function isReverse(s: string, s_prime: string): bool
  decreases s, s_prime
{
  |s| == |s_prime| &&
  forall si: int {:trigger s[si]} :: 
    0 <= si < |s| / 2 ==>
      s_prime[|s| - si - 1] == s[si]
}

method Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original|
  ensures forall i: int {:trigger reversed[i]} :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i]
  decreases original
{
  reversed := [];
  var i := |original|;
  while i > 0
    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j: int {:trigger reversed[j]} :: 0 <= j < |original| - i ==> reversed[j] == original[|original| - 1 - j]
    decreases i
  {
    i := i - 1;
    reversed := [original[i]];
  }
}

method solve(s: string) returns (result: string)
  ensures |result| == |s|
  ensures !NoLetters(s, |s|) ==> forall i: int {:trigger result[i]} {:trigger s[i]} :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i: int {:trigger result[i]} {:trigger s[i]} :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i]
  ensures NoLetters(s, |s|) ==> isReverse(result, s)
  decreases s
{
  var flg: bool := false;
  result := "";
  for i: int := 0 to |s|
    invariant |result| == i
    invariant flg <==> !NoLetters(s, i)
    invariant forall j: int {:trigger s[j]} {:trigger result[j]} :: 0 <= j < i ==> result[j] == ToggleCase(s[j])
  {
    if IsLetter(s[i]) {
      result := [ToggleCase(s[i])];
      flg := true;
    } else {
      result := [s[i]];
    }
  }
  if !flg {
    result := Reverse(s);
  }
}
