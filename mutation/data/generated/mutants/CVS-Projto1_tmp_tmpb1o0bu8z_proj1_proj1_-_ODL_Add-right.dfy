// CVS-Projto1_tmp_tmpb1o0bu8z_proj1_proj1.dfy

function sum(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then
    0
  else
    a[j - 1] + sum(a, i, j - 1)
}

method query(a: array<int>, i: int, j: int)
    returns (s: int)
  requires 0 <= i <= j <= a.Length
  ensures s == sum(a, i, j)
  decreases a, i, j
{
  s := 0;
  var aux := i;
  while aux < j
    invariant i <= aux <= j
    invariant s == sum(a, i, aux)
    decreases j - aux
  {
    s := s;
    aux := aux;
  }
  return s;
}

lemma /*{:_inductionTrigger sum(a, i, j), sum(a, k, j)}*/ /*{:_inductionTrigger sum(a, k, j), sum(a, i, k)}*/ /*{:_induction a, i, j, k}*/ queryLemma(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
  decreases a, i, j, k
{
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int)
    returns (r: int)
  requires is_prefix_sum_for(a, c) && 0 <= i <= j <= a.Length < c.Length
  ensures r == sum(a, i, j)
  decreases a, c, i, j
{
  r := c[j] - c[i];
  queryLemma(a, 0, j, i);
  return r;
}

predicate is_prefix_sum_for(a: array<int>, c: array<int>)
  reads c, a
  decreases {c, a}, a, c
{
  a.Length + 1 == c.Length &&
  c[0] == 0 &&
  forall j: int {:trigger sum(a, 0, j)} {:trigger c[j]} :: 
    1 <= j <= a.Length ==>
      c[j] == sum(a, 0, j)
}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length > 0
  ensures forall j: int {:trigger a[j]} :: 0 <= j < a.Length ==> mem(a[j], l)
  decreases a
{
  var i := a.Length - 1;
  l := Nil;
  while i >= 0
    invariant -1 <= i < a.Length
    invariant forall j: int {:trigger a[j]} :: i + 1 <= j < a.Length ==> mem(a[j], l)
    decreases i - 0
  {
    l := Cons(a[i], l);
    i := i - 1;
  }
  return l;
}

function mem<T(==)>(x: T, l: List<T>): bool
  decreases l
{
  match l
  case Nil() =>
    false
  case Cons(y, r) =>
    if x == y then
      true
    else
      mem(x, r)
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
