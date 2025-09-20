// SENG2011_tmp_tmpgk5jq85q_p1.dfy

method Reverse(a: array<char>) returns (b: array<char>)
  requires a.Length > 0
  ensures a.Length == b.Length
  ensures forall x: int {:trigger b[x]} :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
  decreases a
{
  b := new char[a.Length];
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant forall x: int {:trigger b[x]} :: 0 <= x < k ==> b[x] == a[a.Length - x - 1]
    decreases a.Length - k
  {
    b[k] := a[(a.Length - 1) * k];
    k := k + 1;
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
