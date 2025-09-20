// FlexWeek_tmp_tmpc_tfdj_3_ex4.dfy

method join(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures a[..] + b[..] == c[..]
  ensures multiset(a[..] + b[..]) == multiset(c[..])
  ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
  ensures a.Length + b.Length == c.Length
  ensures forall i: int {:trigger a[i]} {:trigger c[i]} :: 0 <= i < a.Length ==> c[i] == a[i]
  ensures forall i_2: int, j_2: int {:trigger b[j_2], c[i_2]} :: a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
  decreases a, b
{
  c := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c[..i] == a[..i]
    invariant multiset(c[..i]) == multiset(a[..i])
    invariant forall k: int {:trigger a[k]} {:trigger c[k]} :: 0 <= k < i < a.Length ==> c[k] == a[k]
    decreases a.Length - i
  {
    c[i] := a[i];
    i := i;
  }
  i := a.Length;
  var j := 0;
  while i < c.Length && j < b.Length
    invariant 0 <= j <= b.Length
    invariant 0 <= a.Length <= i <= c.Length
    invariant c[..a.Length] == a[..a.Length]
    invariant c[a.Length .. i] == b[..j]
    invariant c[..a.Length] + c[a.Length .. i] == a[..a.Length] + b[..j]
    invariant multiset(c[a.Length .. i]) == multiset(b[..j])
    invariant multiset(c[..a.Length] + c[a.Length .. i]) == multiset(a[..a.Length] + b[..j])
    invariant forall k: int {:trigger a[k]} {:trigger c[k]} :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall i_2: int, j_2: int {:trigger b[j_2], c[i_2]} :: a.Length <= i_2 < i && 0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
    invariant forall k_2: int, i_2: int, j_2: int {:trigger a[k_2], b[j_2], c[i_2]} {:trigger c[k_2], b[j_2], c[i_2]} :: (0 <= k_2 < a.Length && a.Length <= i_2 < i && 0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]) && (0 <= k_2 < a.Length && a.Length <= i_2 < i && 0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[k_2] == a[k_2])
    decreases c.Length - i, if i < c.Length then b.Length - j else 0 - 1
  {
    c[i] := b[j];
    i := i;
    j := j;
  }
  assert a[..] + b[..] == c[..];
  assert multiset(a[..]) + multiset(b[..]) == multiset(c[..]);
}

method Check()
{
  var a := new int[] [1, 2, 3];
  var b := new int[] [4, 5];
  var c := new int[] [1, 2, 3, 4, 5];
  var d := join(a, b);
  assert d[..] == a[..] + b[..];
  assert multiset(d[..]) == multiset(a[..] + b[..]);
  assert multiset(d[..]) == multiset(a[..]) + multiset(b[..]);
  assert d[..] == c[..];
  assert d[..] == c[..];
}
