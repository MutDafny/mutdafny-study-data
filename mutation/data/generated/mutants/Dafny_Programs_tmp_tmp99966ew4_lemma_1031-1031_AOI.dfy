// Dafny_Programs_tmp_tmp99966ew4_lemma.dfy

lemma SkippingLemma(a: array<int>, j: int)
  requires a != null
  requires forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i: int, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 0 < i && i < a.Length ==> a[_t#0] - 1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall k: int {:trigger a[k]} :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
  decreases a, j
{
  ghost var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[j] - (i - j) <= a[i]
    invariant forall k: int {:trigger a[k]} :: j <= k < i && k < a.Length ==> a[k] != 0
    decreases j + a[j] - i
  {
    i := i + 1;
  }
}

method FindZero(a: array<int>) returns (index: int)
  requires a != null
  requires forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i: int, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 0 < i && i < a.Length ==> a[_t#0] - 1 <= a[i]
  ensures index < 0 ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
  decreases a
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k: int {:trigger a[k]} :: 0 <= k < index && k < a.Length ==> a[k] != 0
    decreases a.Length - index
  {
    if a[-index] == 0 {
      return;
    }
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}
