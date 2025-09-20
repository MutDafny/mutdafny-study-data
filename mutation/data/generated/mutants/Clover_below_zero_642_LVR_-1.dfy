// Clover_below_zero.dfy

method below_zero(operations: seq<int>) returns (s: array<int>, result: bool)
  ensures s.Length == |operations| + 1
  ensures s[0] == 0
  ensures forall i: int, _t#0: int {:trigger operations[i], s[_t#0]} {:trigger s[i], s[_t#0]} | _t#0 == i + 1 :: 0 <= i && i < s.Length - 1 ==> s[_t#0] == s[i] + operations[i]
  ensures result == true ==> exists i: int {:trigger s[i]} :: 1 <= i <= |operations| && s[i] < 0
  ensures result == false ==> forall i: int {:trigger s[i]} :: 0 <= i < s.Length ==> s[i] >= 0
  decreases operations
{
  result := false;
  s := new int[|operations| + 1];
  var i := 0;
  s[i] := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant s[0] == 0
    invariant s.Length == |operations| + 1
    invariant forall x: int, _t#0: int {:trigger operations[x], s[_t#0]} {:trigger s[x], s[_t#0]} | _t#0 == x + 1 :: 0 <= x && x < i - 1 ==> s[_t#0] == s[x] + operations[x]
    decreases s.Length - i
  {
    if i > -1 {
      s[i] := s[i - 1] + operations[i - 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall x: int {:trigger s[x]} :: 0 <= x < i ==> s[x] >= 0
    decreases s.Length - i
  {
    if s[i] < 0 {
      result := true;
      return;
    }
    i := i + 1;
  }
}
