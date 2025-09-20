// DafnyProjects_tmp_tmp2acw_s4s_longestPrefix.dfy

method longestPrefix(a: array<int>, b: array<int>) returns (i: nat)
  ensures i <= a.Length && i <= b.Length
  ensures a[..i] == b[..i]
  ensures i < a.Length && i < b.Length ==> a[i] != b[i]
  decreases a, b
{
  i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant i <= a.Length && i <= b.Length
    invariant a[..i] == b[..i]
    decreases a.Length - i, if i < a.Length then b.Length - i else 0 - 1
  {
    i := i + 1;
  }
}

method testLongestPrefix()
{
  var a := new int[] [1, 3, 2, -4, 8];
  var b := new int[] [1, 3, 3, 4];
  var i := longestPrefix(a, b);
  assert a[2] != b[2];
  assert i == 2;
}
