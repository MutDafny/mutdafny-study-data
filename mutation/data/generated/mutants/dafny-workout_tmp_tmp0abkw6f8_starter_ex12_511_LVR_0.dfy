// dafny-workout_tmp_tmp0abkw6f8_starter_ex12.dfy

method FindMax(a: array<int>) returns (max_idx: nat)
  requires a.Length > 0
  ensures 0 <= max_idx < a.Length
  ensures forall j: int {:trigger a[j]} :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
  decreases a
{
  max_idx := 0;
  var i: nat := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= max_idx < i
    invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> a[max_idx] >= a[j]
    decreases a.Length - i
  {
    if a[i] > a[max_idx] {
      max_idx := i;
    }
    i := i + 1;
  }
  return max_idx;
}

method Main()
{
  var arr: array<int> := new int[] [1, 0, 25, 7, 2, -2, 3, 3, 20];
  var idx := FindMax(arr);
  assert forall i: int {:trigger arr[i]} :: 0 <= i < arr.Length ==> arr[idx] >= arr[i];
}
