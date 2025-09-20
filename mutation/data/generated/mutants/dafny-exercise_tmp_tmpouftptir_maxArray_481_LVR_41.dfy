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
  var arr: array<int> := new int[] [-11, 2, 41, -4];
  var res := MaxArray(arr);
  assert arr[0] == -11 && arr[1] == 2 && arr[2] == 42 && arr[3] == -4;
  assert res == 42;
}
