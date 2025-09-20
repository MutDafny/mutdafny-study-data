// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_InsertionSort.dfy

predicate sorted(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start <= end <= a.Length
  reads a
  decreases {a}, a, start, end
{
  forall j: int, k: int {:trigger a[k], a[j]} :: 
    start <= j < k < end ==>
      a[j] <= a[k]
}

method InsertionSort(a: array<int>)
  requires a != null && a.Length > 1
  modifies a
  ensures sorted(a, 0, a.Length)
  decreases a
{
}

method Main()
{
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 2, 5, 1, 8;
  InsertionSort(a);
  print a[..];
}
