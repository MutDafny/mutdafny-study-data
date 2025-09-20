// dafny-synthesis_task_id_644.dfy

method Reverse(a: array<int>)
  modifies a
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
  decreases a
{
  var l := a.Length - 1;
  var i := 0;
  while i < l - i
    invariant 0 <= i <= (l + 1) / 2
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i || l - i < k <= l ==> a[k] == old(a[l - k])
    invariant forall k: int {:trigger old(a[k])} {:trigger a[k]} :: i <= k <= l - i ==> a[k] == old(a[k])
    decreases l - i - i
  {
    a[i], a[l - i] := a[l - i], a[i];
    i := i + 1;
  }
}

method ReverseUptoK(s: array<int>, k: int)
  requires 2 <= k <= s.Length
  modifies s
  ensures forall i: int {:trigger s[i]} :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
  ensures forall i: int {:trigger old(s[i])} {:trigger s[i]} :: k <= i < s.Length ==> s[i] == old(s[i])
  decreases s, k
{
  var l := k - 1;
  var i := 0;
  while i < 0
    invariant 0 <= i <= (l + 1) / 2
    invariant forall p: int {:trigger s[p]} :: 0 <= p < i || l - i < p <= l ==> s[p] == old(s[l - p])
    invariant forall p: int {:trigger old(s[p])} {:trigger s[p]} :: i <= p <= l - i ==> s[p] == old(s[p])
    invariant forall p: int {:trigger old(s[p])} {:trigger s[p]} :: k <= p < s.Length ==> s[p] == old(s[p])
    decreases 0 - i
  {
    s[i], s[l - i] := s[l - i], s[i];
    i := i + 1;
  }
}
