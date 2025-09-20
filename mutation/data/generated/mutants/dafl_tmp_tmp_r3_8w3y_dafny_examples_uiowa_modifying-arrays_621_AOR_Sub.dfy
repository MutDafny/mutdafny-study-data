// dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_modifying-arrays.dfy

method SetEndPoints(a: array<int>, left: int, right: int)
  requires a.Length != 0
  modifies a
  decreases a, left, right
{
  a[0] := left;
  a[a.Length - 1] := right;
}

method Aliases(a: array<int>, b: array<int>)
  requires a.Length >= b.Length > 100
  modifies a
  decreases a, b
{
  a[0] := 10;
  var c := a;
  if b == a {
    b[10] := b[0] + 1;
  }
  c[20] := a[14] - 2;
}

method NewArray() returns (a: array<int>)
  ensures a.Length == 20
  ensures fresh(a)
{
  a := new int[20];
  var b := new int[30];
  a[6] := 216;
  b[7] := 343;
}

method Caller()
{
  var a := NewArray();
  a[8] := 512;
}

method InitArray<T>(a: array<T>, d: T)
  modifies a
  ensures forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == d
  decreases a
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger a[i]} :: 0 <= i < n ==> a[i] == d
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    a[n] := d;
    n := n + 1;
  }
}

method UpdateElements(a: array<int>)
  requires a.Length == 10
  modifies a
  ensures old(a[4]) < a[4]
  ensures a[6] <= old(a[6])
  ensures a[8] == old(a[8])
  decreases a
{
  a[4] := a[4] + 3;
  a[8] := a[8] + 1;
  a[7] := 516;
  a[8] := a[8] - 1;
}

method IncrementArray(a: array<int>)
  modifies a
  ensures forall i: int {:trigger old(a[i])} {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  decreases a
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger old(a[i])} {:trigger a[i]} :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i: int {:trigger old(a[i])} {:trigger a[i]} :: n <= i < a.Length ==> a[i] == old(a[i])
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    a[n] := a[n] + 1;
    n := n + 1;
  }
}

method CopyArray<T>(a: array<T>, b: array<T>)
  requires a.Length == b.Length
  modifies b
  ensures forall i: int {:trigger old(a[i])} {:trigger b[i]} :: 0 <= i < a.Length ==> b[i] == old(a[i])
  decreases a, b
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int {:trigger old(a[i])} {:trigger b[i]} :: 0 <= i < n ==> b[i] == old(a[i])
    invariant forall i: int {:trigger old(a[i])} {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] == old(a[i])
    decreases if n <= a.Length then a.Length - n else n - a.Length
  {
    b[n] := a[n];
    n := n + 1;
  }
}
