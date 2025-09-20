// assertive-programming-assignment-1_tmp_tmp3h_cj44u_FindRange.dfy

method Main()
{
}

predicate Sorted(q: seq<int>)
  decreases q
{
  forall i: int, j: int {:trigger q[j], q[i]} :: 
    0 <= i <= j < |q| ==>
      q[i] <= q[j]
}

method {:verify true} FindRange(q: seq<int>, key: int)
    returns (left: nat, right: nat)
  requires Sorted(q)
  ensures left <= right <= |q|
  ensures forall i: int {:trigger q[i]} :: 0 <= i < left ==> q[i] < key
  ensures forall i: int {:trigger q[i]} :: left <= i < right ==> q[i] == key
  ensures forall i: int {:trigger q[i]} :: right <= i < |q| ==> q[i] > key
  decreases q, key
{
  left := BinarySearch(q, key, 0, |q|, (n: int, m: int) => n >= m);
  right := BinarySearch(q, key, left, |q|, (n: int, m: int) => n > m);
}

predicate RangeSatisfiesComparer(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
  requires 0 <= lowerBound <= upperBound <= |q|
  decreases q, key, lowerBound, upperBound
{
  forall i: int {:trigger q[i]} :: 
    lowerBound <= i < upperBound ==>
      comparer(q[i], key)
}

predicate RangeSatisfiesComparerNegation(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
  requires 0 <= lowerBound <= upperBound <= |q|
  decreases q, key, lowerBound, upperBound
{
  RangeSatisfiesComparer(q, key, lowerBound, upperBound, (n1: int, n2: int) => !comparer(n1, n2))
}

method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
    returns (index: nat)
  requires Sorted(q)
  requires 0 <= lowerBound <= upperBound <= |q|
  requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
  requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
  requires (forall n1: int, n2: int {:trigger comparer(n1, n2)} :: comparer(n1, n2) == (n1 > n2)) || forall n1: int, n2: int {:trigger comparer(n1, n2)} :: comparer(n1, n2) == (n1 >= n2)
  ensures lowerBound <= index <= upperBound
  ensures RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
  ensures RangeSatisfiesComparer(q, key, index, |q|, comparer)
  decreases q, key, lowerBound, upperBound
{
  var low: nat := lowerBound;
  var high: nat := upperBound;
  while low < high
    invariant lowerBound <= low <= high <= upperBound
    invariant RangeSatisfiesComparerNegation(q, key, 0, low, comparer)
    invariant RangeSatisfiesComparer(q, key, high, |q|, comparer)
    decreases high - low
  {
    var middle := low + (high - low) / 2;
    if comparer(q[middle], key) {
      high := middle;
    } else {
      low := middle + 1;
    }
  }
  index := high;
}
