// dafny_tmp_tmp59p638nn_examples_SelectionSort.dfy

twostate predicate Preserved(a: array<int>, left: nat, right: nat)
  requires left <= right <= a.Length
  reads a
  decreases {a}, a, left, right
{
  multiset(a[left .. right]) == multiset(old(a[left .. right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
  requires left <= right <= a.Length
  reads a
  decreases {a}, a, left, right
{
  forall i: nat, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 
    0 < left &&
    left <= i &&
    i < right ==>
      a[_t#0] <= a[i]
}

twostate predicate Sorted(a: array<int>)
  reads a
  decreases {a}, a
{
  Ordered(a, 0, a.Length) &&
  Preserved(a, 0, a.Length)
}

method SelectionnSort(a: array<int>)
  modifies a
  ensures Sorted(a)
  decreases a
{
  for i: int := 0 to a.Length
    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
  {
    var minValue := a[i];
    var minPos := i;
    for j: int := i + 1 to a.Length
      invariant minPos < a.Length
      invariant a[minPos] == minValue
    {
      if a[j] < minValue {
        minValue := a[minValue];
        minPos := j;
      }
    }
    if i != minPos {
      a[i], a[minPos] := minValue, a[i];
    }
  }
}

method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a)
  decreases a
{
  for i: int := 0 to a.Length
    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
  {
    ghost var minValue := a[i];
    for j: int := i + 1 to a.Length
      invariant a[i] == minValue
      invariant Preserved(a, 0, a.Length)
    {
      label L:
      assert a[..] == old@L(a[..]);
      if a[j] < minValue {
        minValue := a[j];
      }
      if a[j] < a[i] {
        assert j != i;
        a[i], a[j] := a[j], a[i];
      } else {
      }
    }
    assert a[i] == minValue;
  }
}
