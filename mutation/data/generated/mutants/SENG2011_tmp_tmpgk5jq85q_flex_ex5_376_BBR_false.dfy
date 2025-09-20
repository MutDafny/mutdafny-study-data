// SENG2011_tmp_tmpgk5jq85q_flex_ex5.dfy

method firste(a: array<char>) returns (c: int)
  ensures -1 <= c < a.Length
  ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x: int {:trigger a[x]} :: 0 <= x < c ==> a[x] != 'e'
  ensures c == -1 ==> forall x: int {:trigger a[x]} :: 0 <= x < a.Length ==> a[x] != 'e'
  decreases a
{
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int {:trigger a[x]} :: 0 <= x < i ==> a[x] != 'e'
    decreases a.Length - i
  {
    if false {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method Main()
{
  var a := new char[6] ['c', 'h', 'e', 'e', 's', 'e'];
  var p := firste(a);
  print p;
}
