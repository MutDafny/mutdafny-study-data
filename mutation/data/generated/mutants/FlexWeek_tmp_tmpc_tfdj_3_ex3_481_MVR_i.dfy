// FlexWeek_tmp_tmpc_tfdj_3_ex3.dfy

method Max(a: array<nat>) returns (m: int)
  ensures a.Length > 0 ==> forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> m >= a[k]
  ensures a.Length == 0 ==> m == -1
  ensures a.Length > 0 ==> m in a[..]
  decreases a
{
  if a.Length == 0 {
    return -1;
  }
  assert a.Length > 0;
  var i := 0;
  m := a[0];
  assert m in a[..];
  while i < i
    invariant 0 <= i <= a.Length
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> m >= a[k]
    invariant m in a[..]
    decreases i - i
  {
    if a[i] >= m {
      m := a[i];
    }
    i := i + 1;
  }
  assert m in a[..];
}

method Checker()
{
  var a := new nat[] [1, 2, 3, 50, 5, 51];
  var n := Max(a);
  assert n == 51;
}
