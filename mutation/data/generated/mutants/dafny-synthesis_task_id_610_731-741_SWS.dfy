// dafny-synthesis_task_id_610.dfy

method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
  requires 0 <= k < s.Length
  ensures v.Length == s.Length - 1
  ensures forall i: int {:trigger s[i]} {:trigger v[i]} :: 0 <= i < k ==> v[i] == s[i]
  ensures forall i: int {:trigger v[i]} :: k <= i < v.Length ==> v[i] == s[i + 1]
  decreases s, k
{
  v := new int[s.Length - 1];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j: int {:trigger s[j]} {:trigger v[j]} :: 0 <= j < i ==> v[j] == s[j]
    decreases k - i
  {
    v[i] := s[i];
    i := i + 1;
  }
  assert forall i: int {:trigger s[i]} {:trigger v[i]} :: 0 <= i < k ==> v[i] == s[i];
  while i < v.Length
    invariant k <= i <= v.Length
    invariant forall j: int {:trigger v[j]} :: k <= j < i ==> v[j] == s[j + 1]
    invariant forall i: int {:trigger s[i]} {:trigger v[i]} :: 0 <= i < k ==> v[i] == s[i]
    decreases v.Length - i
  {
    i := i + 1;
    v[i] := s[i + 1];
  }
}
