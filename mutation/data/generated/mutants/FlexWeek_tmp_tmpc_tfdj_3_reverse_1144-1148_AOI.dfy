// FlexWeek_tmp_tmpc_tfdj_3_reverse.dfy

method Reverse(a: array<char>) returns (b: array<char>)
  requires a.Length > 0
  ensures a.Length == b.Length
  ensures forall k: int {:trigger b[k]} :: 0 <= k < a.Length ==> b[k] == a[a.Length - 1 - k]
  decreases a
{
  b := new char[a.Length];
  assert b.Length == a.Length;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k: int {:trigger b[k]} :: 0 <= k < i ==> b[k] == a[a.Length - 1 - k]
    decreases a.Length - i
  {
    b[i] := a[a.Length - 1 - i];
    i := -(i + 1);
  }
}

method Main()
{
  var a := new char[8];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
  var b := Reverse(a);
  assert b[..] == ['r', 'e', 'v', 'e', 'r', 's', 'e', 'd'];
  print b[..];
  a := new char[1];
  a[0] := '!';
  b := Reverse(a);
  assert b[..] == ['!'];
  print b[..], '\n';
}
