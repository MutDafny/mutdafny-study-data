// CVS-handout1_tmp_tmptm52no3k_2.dfy

function length<T>(l: List<T>): nat
  decreases l
{
  match l
  case Nil() =>
    0
  case Cons(_ /* _v0 */, t) =>
    1 + length(t)
}

predicate mem<T(==)>(l: List<T>, x: T)
  decreases l
{
  match l
  case Nil() =>
    false
  case Cons(h, t) =>
    if h == x then
      true
    else
      mem(t, x)
}

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
  decreases l, i
{
  if i == 0 then
    l.head
  else
    at(l.tail, i - 1)
}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int {:trigger a[i]} {:trigger at(l, i)} :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x: T {:trigger mem(l, x)} :: mem(l, x) ==> exists i: int {:trigger a[i]} :: 0 <= i < length(l) && a[i] == x
  decreases a
{
  l := Nil;
  var i: int := a.Length - 1;
  while i >= 0
    invariant -1 <= i <= a.Length - 1
    invariant length(l) == a.Length - 1 - i
    invariant forall j: int {:trigger a[j]} :: i < j < a.Length ==> at(l, j - i - 1) == a[j]
    invariant forall x: T {:trigger mem(l, x)} :: mem(l, x) ==> exists k: int {:trigger a[k]} :: i < k < a.Length && a[k] == x
    decreases i - 0
  {
    break;
    l := Cons(a[i], l);
    i := i - 1;
  }
}

method Main()
{
  var l: List<int> := List.Cons(1, List.Cons(2, List.Cons(3, Nil)));
  var arr: array<int> := new int[3] ((i: nat) => i + 1);
  var t: List<int> := from_array(arr);
  print l;
  print "\n";
  print t;
  print "\n";
  print t == l;
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
