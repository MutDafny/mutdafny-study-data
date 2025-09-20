// dafny_tmp_tmp59p638nn_examples_GenericSelectionSort.dfy

ghost function Sum(x: int): nat
  decreases x
{
  if x <= 0 then
    0
  else
    x + Sum(x - 1)
}

method Main()
{
  var a: array<int> := new int[3];
  a[0] := 2;
  a[1] := 4;
  a[2] := 1;
  var Sort := new Sort<int>((x: int, y: int) => x < y);
  Sort.SelectionSort(a);
  print a[..];
}

trait Comparable<T(==)> {
  function Lt(x: T, y: T): bool
}

trait Sorted<T(==)> extends Comparable<T> {
  ghost predicate Ordered(a: array<T>, left: nat, right: nat)
    requires left <= right <= a.Length
    reads a
    decreases {a}, a, left, right
  {
    forall i: nat, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 
      0 < left &&
      left <= i &&
      i < right ==>
        Lt(a[_t#0], a[i]) || a[_t#0] == a[i]
  }

  twostate predicate Preserved(a: array<T>, left: nat, right: nat)
    requires left <= right <= a.Length
    reads a
    decreases {a}, a, left, right
  {
    multiset(a[left .. right]) == multiset(old(a[left .. right]))
  }

  twostate predicate Sorted(a: array<T>)
    reads a
    decreases {a}, a
  {
    Ordered(a, 0, a.Length) &&
    Preserved(a, 0, a.Length)
  }
}

class Sort<T(==)> extends SelectionSort<T> {
  const CMP: (T, T) -> bool

  constructor (cmp: (T, T) -> bool)
    ensures CMP == cmp
    ensures comparisonCount == 0
  {
    CMP := cmp;
    comparisonCount := 0;
  }

  function Lt(x: T, y: T): bool
  {
    CMP(x, y)
  }
}

trait Measurable<T(==)> extends Comparable<T> {
  ghost var comparisonCount: nat

  method Ltm(x: T, y: T) returns (b: bool)
    modifies this`comparisonCount
    ensures b ==> Lt(x, y)
    ensures comparisonCount == old(comparisonCount) + 1
  {
    comparisonCount := comparisonCount + 1;
    b := Lt(x, y);
  }
}

trait SelectionSort<T(==)> extends Comparable<T>, Measurable<T>, Sorted<T> {
  method SelectionSort(a: array<T>)
    requires comparisonCount == 0
    modifies a, this
    ensures Sorted(a)
    ensures comparisonCount <= a.Length * a.Length
    decreases a
  {
    for i: int := 0 to a.Length
      invariant Ordered(a, 0, i)
      invariant Preserved(a, 0, a.Length)
      invariant comparisonCount == i * a.Length - Sum(i)
    {
      var minPos := i;
      var minValue := a[i];
      assert comparisonCount == i * a.Length - Sum(i) + i + 1 - i - 1;
      for j: int := i + 1 to a.Length
        invariant minPos < a.Length
        invariant a[minPos] == minValue
        invariant Preserved(a, 0, a.Length)
        invariant comparisonCount == i * a.Length - Sum(i) + j - i - 1
      {
        label L:
        var cmp := Ltm(a[j], minValue);
        assert a[..] == old@L(a[..]);
        if cmp {
          minValue := a[j];
          minPos := j;
        }
        assert i * a.Length - Sum(i) + j - i - 1 + 1 == i * a.Length - Sum(i) + j + 1 - i - 1;
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
      }
      assert comparisonCount == (i + 1) * a.Length - Sum(i + 1);
    }
  }
}
