// SENG2011_tmp_tmpgk5jq85q_ass1_ex8.dfy

method GetEven(a: array<nat>)
  requires true
  modifies a
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] % 2 == 0
  decreases a
{
  var i := 0;
  while i > a.Length
    invariant 0 <= i <= a.Length && forall j: int {:trigger a[j]} :: 0 <= j < i ==> a[j] % 2 == 0
    decreases a.Length - i
  {
    if a[i] % 2 != 0 {
      a[i] := a[i] + 1;
    }
    i := i + 1;
  }
}
