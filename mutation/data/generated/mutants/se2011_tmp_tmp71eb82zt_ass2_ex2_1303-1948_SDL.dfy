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
}
