// DafnyProjects_tmp_tmp2acw_s4s_longestPrefix.dfy

method longestPrefix(a: array<int>, b: array<int>) returns (i: nat)
  ensures i <= a.Length && i <= b.Length
  ensures a[..i] == b[..i]
  ensures i < a.Length && i < b.Length ==> a[i] != b[i]
  decreases a, b
{
  i := 0;
  while a[i] == b[i]
    invariant i <= a.Length && i <= b.Length
    invariant a[..i] == b[..i]
  {
    i := i + 1;
  }
}

method testLongestPrefix()
{
  var a := new int[] [1, 3, 2, 4, 8];
  var b := new int[] [1, 3, 3, 4];
  var i := longestPrefix(a, b);
  assert a[2] != b[2];
  assert i == 2;
}
