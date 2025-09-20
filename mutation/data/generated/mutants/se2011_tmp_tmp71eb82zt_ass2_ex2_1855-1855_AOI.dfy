// se2011_tmp_tmp71eb82zt_ass2_ex2.dfy

method SecondLargest(a: array<int>) returns (seclar: int)
  requires a.Length > 0
  decreases a
{
  if a.Length == 1 {
    seclar := a[0];
  } else {
    var l, s, i: int := 0, 0, 0;
    if a[1] > a[0] {
      l := a[1];
      s := a[0];
    } else {
      l := a[0];
      s := a[1];
    }
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> l >= a[j]
      invariant s <= l
      decreases a.Length - i
    {
      if a[i] > l {
        s := l;
        l := a[i];
      }
      if a[i] > s && a[i] < l {
        s := a[i];
      }
      if s == l && s > a[i] {
        s := a[i];
      }
      i := i + 1;
    }
    seclar := s;
  }
}

method Main()
{
  var a: array<int> := new int[] [1];
  assert a[0] == 1;
  var x: int := SecondLargest(a);
  var b: array<int> := new int[] [9, 1];
  assert b[0] == 9 && b[1] == 1;
  x := SecondLargest(b);
  var c: array<int> := new int[] [1, 9];
  assert c[0] == 1 && c[1] == 9;
  x := SecondLargest(c);
  var d: array<int> := new int[] [2, 42, -4, 123, 42];
  assert d[0] == 2 && d[1] == 42 && d[2] == -4 && d[3] == 123 && d[4] == 42;
  x := SecondLargest(d);
  var e: array<int> := new int[] [1, -9, 8];
  assert e[0] == 1 && e[1] == 9 && e[2] == 8;
  x := SecondLargest(e);
}
