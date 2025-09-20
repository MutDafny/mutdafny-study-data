// FMSE-2022-2023_tmp_tmp6_x_ba46_Lab10_Lab10.dfy

predicate IsOdd(x: int)
  decreases x
{
  x % 2 == 1
}

newtype Odd = n: int
  | IsOdd(n)
  witness 3

trait OddListSpec {
  var s: seq<Odd>
  var capacity: nat

  predicate Valid()
    reads this
    decreases {this}
  {
    0 <= |s| <= this.capacity &&
    forall i: int {:trigger s[i]} :: 
      0 <= i < |s| ==>
        IsOdd(s[i] as int)
  }

  method insert(index: nat, element: Odd)
    requires 0 <= index <= |s|
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[index] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index, element

  method pushFront(element: Odd)
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[0] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element

  method pushBack(element: Odd)
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[|s| - 1] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element

  method remove(element: Odd)
    requires Valid()
    requires |s| > 0
    requires element in s
    modifies this
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element

  method removeAtIndex(index: nat)
    requires Valid()
    requires |s| > 0
    requires 0 <= index < |s|
    modifies this
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index

  method popFront() returns (x: Odd)
    requires Valid()
    requires |s| > 0
    modifies this
    ensures old(s)[0] == x
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()

  method popBack() returns (x: Odd)
    requires Valid()
    requires |s| > 0
    modifies this
    ensures old(s)[|old(s)| - 1] == x
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()

  method length() returns (n: nat)
    ensures n == |s|

  method at(index: nat) returns (x: Odd)
    requires 0 <= index < |s|
    decreases index

  method BinarySearch(element: Odd) returns (index: int)
    requires forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures 0 <= index ==> index < |s| && s[index] == element
    ensures index == -1 ==> element !in s[..]
    decreases element

  method mergedWith(l2: OddList) returns (l: OddList)
    requires Valid()
    requires l2.Valid()
    requires this.capacity >= 0
    requires l2.capacity >= 0
    requires forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i: int, j: int {:trigger l2.s[j], l2.s[i]} :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
    ensures l.capacity == this.capacity + l2.capacity
    ensures |l.s| == |s| + |l2.s|
    decreases l2
}

class OddList extends OddListSpec {
  constructor (capacity: nat)
    ensures Valid()
    ensures |s| == 0
    ensures this.capacity == capacity
    decreases capacity
  {
    s := [];
    this.capacity := capacity;
  }

  method insert(index: nat, element: Odd)
    requires 0 <= index <= |s|
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[index] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index, element
  {
    var tail := s[index..];
    s := s[..index] + [element];
    s := s + tail;
  }

  method pushFront(element: Odd)
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[0] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element
  {
    insert(0, element);
  }

  method pushBack(element: Odd)
    requires |s| + 1 <= this.capacity
    modifies this
    ensures |s| == |old(s)| + 1
    ensures s[|s| - 1] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element
  {
    insert(|s|, element);
  }

  method remove(element: Odd)
    requires Valid()
    requires |s| > 0
    requires element in s
    modifies this
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases element
  {
    for i: int := 0 to |s|
      invariant 0 <= i <= |s|
      invariant forall k: int {:trigger s[k]} :: 0 <= k < i ==> s[k] != element
    {
      if s[i] == element {
        s := s[..i] + s[i + 1..];
        break;
      }
    }
  }

  method removeAtIndex(index: nat)
    requires Valid()
    requires |s| > 0
    requires 0 <= index < |s|
    modifies this
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index
  {
    s := s[..index] + s[index + 1..];
  }

  method popFront() returns (x: Odd)
    requires Valid()
    requires |s| > 0
    modifies this
    ensures old(s)[0] == x
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
  {
    x := s[0];
    s := s[1..];
  }

  method popBack() returns (x: Odd)
    requires Valid()
    requires |s| > 0
    modifies this
    ensures old(s)[|old(s)| - 1] == x
    ensures |s| == |old(s)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
  {
    x := s[|s| - 1];
    s := s[..|s| - 1];
  }

  method length() returns (n: nat)
    ensures n == |s|
  {
    return |s|;
  }

  method at(index: nat) returns (x: Odd)
    requires 0 <= index < |s|
    ensures s[index] == x
    decreases index
  {
    return s[index];
  }

  method BinarySearch(element: Odd) returns (index: int)
    requires forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures 0 <= index ==> index < |s| && s[index] == element
    ensures index == -1 ==> element !in s[..]
    decreases element
  {
    var left, right := 0, |s|;
    while left < right
      invariant 0 <= left <= right <= |s|
      invariant element !in s[..left] && element !in s[right..]
      decreases right - left
    {
      var mid := (left + right) / 2;
      if element < s[mid] {
        right := mid;
      } else if s[mid] < element {
        left := mid + 1;
      } else {
        return mid;
      }
    }
    return -1;
  }

  method mergedWith(l2: OddList) returns (l: OddList)
    requires Valid()
    requires l2.Valid()
    requires this.capacity >= 0
    requires l2.capacity >= 0
    requires forall i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i: int, j: int {:trigger l2.s[j], l2.s[i]} :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
    ensures l.capacity == this.capacity + l2.capacity
    ensures |l.s| == |s| + |l2.s|
    decreases l2
  {
    l := new OddList(this.capacity + l2.capacity);
    var i, j := 0, 0;
    while i < |s| || j != |l2.s|
      invariant 0 <= i <= |s|
      invariant 0 <= j <= |l2.s|
      invariant i + j == |l.s|
      invariant |l.s| <= l.capacity
      invariant l.capacity == this.capacity + l2.capacity
      decreases |s| - i, |l2.s| - j
    {
      if i == |s| {
        if j == |l2.s| {
          return l;
        } else {
          l.pushBack(l2.s[j]);
          j := j + 1;
        }
      } else {
        if j == |l2.s| {
          l.pushBack(s[i]);
          i := i + 1;
        } else {
          if s[i] < l2.s[j] {
            l.pushBack(s[i]);
            i := i + 1;
          } else {
            l.pushBack(l2.s[j]);
            j := j + 1;
          }
        }
      }
    }
    return l;
  }
}

trait CircularLinkedListSpec<T(==)> {
  var l: seq<T>
  var capacity: nat

  predicate Valid()
    reads this
    decreases {this}
  {
    0 <= |l| <= this.capacity
  }

  method insert(index: int, element: T)
    requires |l| + 1 <= this.capacity
    modifies this
    ensures |old(l)| == 0 ==> l == [element]
    ensures |l| == |old(l)| + 1
    ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index

  method remove(element: T)
    requires Valid()
    requires |l| > 0
    requires element in l
    modifies this
    ensures |l| == |old(l)| - 1
    ensures old(capacity) == capacity
    ensures Valid()

  method removeAtIndex(index: int)
    requires Valid()
    requires |l| > 0
    modifies this
    ensures |l| == |old(l)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index

  method length() returns (n: nat)
    ensures n == |l|

  method at(index: int) returns (x: T)
    requires |l| > 0
    ensures l[index % |l|] == x
    decreases index

  method nextAfter(index: int) returns (x: T)
    requires |l| > 0
    ensures |l| == 1 ==> x == l[0]
    ensures |l| > 1 && index % |l| == |l| - 1 ==> x == l[0]
    ensures |l| > 1 && 0 <= index && |l| < |l| - 1 ==> x == l[index % |l| + 1]
    decreases index
}

class CircularLinkedList<T(==)> extends CircularLinkedListSpec<T> {
  constructor (capacity: nat)
    requires capacity >= 0
    ensures Valid()
    ensures |l| == 0
    ensures this.capacity == capacity
    decreases capacity
  {
    l := [];
    this.capacity := capacity;
  }

  method insert(index: int, element: T)
    requires |l| + 1 <= this.capacity
    modifies this
    ensures |old(l)| == 0 ==> l == [element]
    ensures |l| == |old(l)| + 1
    ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index
  {
    if |l| == 0 {
      l := [element];
    } else {
      var actualIndex := index % |l|;
      var tail := l[actualIndex..];
      l := l[..actualIndex] + [element];
      l := l + tail;
    }
  }

  method remove(element: T)
    requires Valid()
    requires |l| > 0
    requires element in l
    modifies this
    ensures |l| == |old(l)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
  {
    for i: nat := 0 to |l|
      invariant 0 <= i <= |l|
      invariant forall k: int {:trigger l[k]} :: 0 <= k < i ==> l[k] != element
    {
      if l[i] == element {
        l := l[..i] + l[i + 1..];
        break;
      }
    }
  }

  method removeAtIndex(index: int)
    requires Valid()
    requires |l| > 0
    modifies this
    ensures |l| == |old(l)| - 1
    ensures old(capacity) == capacity
    ensures Valid()
    decreases index
  {
    var actualIndex := index % |l|;
    l := l[..actualIndex] + l[actualIndex + 1..];
  }

  method length() returns (n: nat)
    ensures n == |l|
  {
    return |l|;
  }

  method at(index: int) returns (x: T)
    requires |l| > 0
    ensures l[index % |l|] == x
    decreases index
  {
    var actualIndex := index % |l|;
    return l[actualIndex];
  }

  method nextAfter(index: int) returns (x: T)
    requires |l| > 0
    ensures |l| == 1 ==> x == l[0]
    ensures |l| > 1 && index % |l| == |l| - 1 ==> x == l[0]
    ensures |l| > 1 && 0 <= index && |l| < |l| - 1 ==> x == l[index % |l| + 1]
    decreases index
  {
    if |l| == 1 {
      x := l[0];
    } else {
      var actualIndex := index % |l|;
      if actualIndex == |l| - 1 {
        x := l[0];
      } else {
        x := l[actualIndex + 1];
      }
    }
    return x;
  }

  method isIn(element: T) returns (b: bool)
    ensures |l| == 0 ==> b == false
    ensures |l| > 0 && b == true ==> exists i: int {:trigger l[i]} :: 0 <= i < |l| && l[i] == element
    ensures |l| > 0 && b == false ==> !exists i: int {:trigger l[i]} :: 0 <= i < |l| && l[i] == element
  {
    if |l| == 0 {
      b := false;
    } else {
      b := false;
      for i: nat := 0 to |l|
        invariant 0 <= i <= |l|
        invariant forall k: int {:trigger l[k]} :: 0 <= k < i ==> l[k] != element
      {
        if l[i] == element {
          b := true;
          break;
        }
      }
    }
  }
}
