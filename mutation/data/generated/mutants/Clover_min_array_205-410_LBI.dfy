// Clover_min_array.dfy

method minArray(a: array<int>) returns (r: int)
  requires a.Length > 0
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i: int {:trigger a[i]} :: 0 <= i < a.Length && r == a[i]
  decreases a
{
  r := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int {:trigger a[x]} :: 0 <= x < i ==> r <= a[x]
    invariant exists x: int {:trigger a[x]} :: 0 <= x < i && r == a[x]
    decreases a.Length - i
  {
    break;
    if r > a[i] {
      r := a[i];
    }
    i := i + 1;
  }
}
