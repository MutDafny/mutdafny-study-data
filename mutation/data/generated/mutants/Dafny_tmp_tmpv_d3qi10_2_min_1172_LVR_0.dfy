// Dafny_tmp_tmpv_d3qi10_2_min.dfy

function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
  decreases a, b
{
  if a < b then
    a
  else
    b
}

method minMethod(a: int, b: int) returns (c: int)
  ensures c <= a && c <= b
  ensures c == a || c == b
  ensures c == min(a, b)
  decreases a, b
{
  if a < b {
    c := a;
  } else {
    c := b;
  }
}

ghost function minFunction(a: int, b: int): int
  ensures minFunction(a, b) <= a && minFunction(a, b) <= b
  ensures minFunction(a, b) == a || minFunction(a, b) == b
  decreases a, b
{
  if a < b then
    a
  else
    b
}

method minArray(a: array<int>) returns (m: int)
  requires a != null && a.Length > 0
  ensures forall k: int {:trigger a[k]} | 0 <= k < a.Length :: m <= a[k]
  ensures exists k: int {:trigger a[k]} | 0 <= k < a.Length :: m == a[k]
  decreases a
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k: int {:trigger a[k]} | 0 <= k < i :: m <= a[k]
    invariant exists k: int {:trigger a[k]} | 0 <= k < i :: m == a[k]
    decreases a.Length - i
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 0;
  }
}

method Main()
{
  var integer := min(1, 2);
  print integer;
}
