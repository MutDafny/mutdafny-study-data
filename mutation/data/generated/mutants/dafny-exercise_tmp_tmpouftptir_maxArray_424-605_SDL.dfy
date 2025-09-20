// dafny-exercise_tmp_tmpouftptir_maxArray.dfy

method MaxArray(a: array<int>) returns (max: int)
  requires a.Length > 0
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] <= max
  ensures exists i: int {:trigger a[i]} :: 0 <= i < a.Length && a[i] == max
  decreases a
{
  var i: nat := 1;
  max := a[0];
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> a[j] <= max
    invariant exists j: int {:trigger a[j]} :: 0 <= j < i && a[j] == max
    decreases a.Length - i
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}

method Main()
{
}
