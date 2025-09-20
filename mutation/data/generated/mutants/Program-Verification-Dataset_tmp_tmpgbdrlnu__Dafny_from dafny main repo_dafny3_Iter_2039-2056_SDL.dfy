// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_Iter.dfy

method Client<T(==,0)>(l: List<T>, stop: T) returns (s: seq<T>)
  requires l.Valid()
  decreases l
{
  var c := new Cell;
  var iter := new M<T>(l, c);
  s := [];
  while true
    invariant iter.Valid() && fresh(iter._new)
    invariant iter.xs <= l.Contents
    decreases |l.Contents| - |iter.xs|
  {
    var more := iter.MoveNext();
    if !more {
      break;
    }
    if iter.x == stop {
      return;
    }
  }
}

method PrintSequence<T>(s: seq<T>)
  decreases s
{
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    print s[i], " ";
    i := i + 1;
  }
  print "\n";
}

method Main()
{
  var myList := new List.Init();
  var i := 0;
  while i < 100
    invariant myList.Valid() && fresh(myList.Repr)
    decreases 100 - i
  {
    myList.Add(i);
    i := i + 2;
  }
  var s := Client(myList, 89);
  PrintSequence(s);
  s := Client(myList, 14);
  PrintSequence(s);
}

class List<T> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>
  var a: array<T>
  var n: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this}
  {
    this in Repr &&
    a in Repr &&
    n <= a.Length &&
    Contents == a[..n]
  }

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {
    Contents, n := [], 0;
    a := new T[0];
    Repr := {this, a};
  }

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
  {
    if n == a.Length {
      var b := new T[2 * a.Length + 1] ((i: int) requires 0 <= i reads this, a => if i < a.Length then a[i] else t);
      assert b[..n] == a[..n] == Contents;
      a, Repr := b, Repr + {b};
      assert b[..n] == Contents;
    }
    a[n], n, Contents := t, n + 1, Contents + [t];
  }
}

class Cell {
  var data: int
}

iterator M<T(0)>(l: List<T>, c: Cell) yields (x: T)
  requires l.Valid()
  reads l.Repr
  modifies c
  yield requires true
  yield ensures xs <= l.Contents
  yield ensures x == l.Contents[|xs| - 1]
  ensures xs == l.Contents
  decreases l, c
{
  var i := 0;
  while i < l.n
    invariant i <= l.n && i == |xs| && xs <= l.Contents
    decreases _yieldCount, l.n - i
  {
    if * {
      assert l.Valid();
    }
    if * {
      x := l.a[i];
      yield;
      i := i + 1;
    } else {
      x, i := l.a[i], i + 1;
      yield;
    }
  }
}
