// SENG2011_tmp_tmpgk5jq85q_exam_ex2.dfy

method Getmini(a: array<int>) returns (mini: nat)
  requires a.Length > 0
  ensures 0 <= mini < a.Length
  ensures forall x: int {:trigger a[x]} :: 0 <= x < a.Length ==> a[mini] <= a[x]
  ensures forall x: int {:trigger a[x]} :: 0 <= x < mini ==> a[mini] < a[x]
  decreases a
{
  var min: int := a[0];
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int {:trigger a[x]} :: 0 <= x < i ==> min <= a[x]
    invariant min in a[..]
    decreases a.Length - i
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
  var k: int := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant forall x: int {:trigger a[x]} :: 0 <= x < k ==> min < a[x]
    decreases a.Length - k
  {
    if a[k] == min {
      return k;
    }
  }
}
