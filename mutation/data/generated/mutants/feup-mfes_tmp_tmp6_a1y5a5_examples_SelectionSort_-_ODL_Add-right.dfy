// feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort.dfy

predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
  decreases {a}, a, from, to
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    from <= i < j < to ==>
      a[i] <= a[j]
}

method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases a
{
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall lhs: int, rhs: int {:trigger a[rhs], a[lhs]} :: 0 <= lhs < i <= rhs < a.Length ==> a[lhs] <= a[rhs]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases a.Length - 1 - i
  {
    var j := findMin(a, i, a.Length);
    a[i], a[j] := a[j], a[i];
    i := i;
  }
}

method findMin(a: array<real>, from: nat, to: nat)
    returns (index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k: int {:trigger a[k]} :: from <= k < to ==> a[k] >= a[index]
  decreases a, from, to
{
  var i := from;
  index := from;
  while i < to
    invariant from <= index < i <= to
    invariant forall k: int {:trigger a[k]} :: from <= k < i ==> a[k] >= a[index]
    decreases a.Length - i
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i;
  }
}

method testSelectionSort()
{
  var a := new real[5] [9.0, 4.0, 6.0, 3.0, 8.0];
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0];
  selectionSort(a);
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0];
}

method testFindMin()
{
  var a := new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  var m := findMin(a, 0, 5);
  assert a[3] == 4.0;
  assert m == 3;
}
