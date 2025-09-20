// dafny-duck_tmp_tmplawbgxjo_ex3.dfy

predicate sortedbad(s: string)
  decreases s
{
  forall i: int, j: int {:trigger s[j], s[i]} :: 
    (0 <= i <= j < |s| &&
    s[i] == 'b' &&
    s[j] != 'b' ==>
      i < j) &&
    (0 <= i <= j < |s| &&
    s[i] == 'b' &&
    s[j] != 'b' ==>
      forall i: int, j: int {:trigger s[j], s[i]} :: 
        0 <= i <= j < |s| &&
        s[i] != 'd' &&
        s[j] == 'd' ==>
          i < j)
}

method BadSort(a: string) returns (b: string)
  requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  ensures sortedbad(b)
  ensures multiset(b[..]) == multiset(a[..])
  decreases a
{
  b := a;
  var next: int := 0;
  var aPointer: int := 0;
  var dPointer: int := |b|;
  while next != dPointer
    invariant 0 <= aPointer <= next <= dPointer <= |b|
    invariant forall i: int {:trigger b[i]} :: 0 <= i < aPointer ==> b[i] == 'b'
    invariant forall i: int {:trigger b[i]} :: aPointer <= i < next ==> b[i] == 'a'
    invariant forall i: int {:trigger b[i]} :: dPointer <= i < |b| ==> b[i] == 'd'
    invariant forall i: int {:trigger b[i]} :: 0 <= i < |b| ==> b[i] in {'b', 'a', 'd'}
    invariant sortedbad(b)
    invariant multiset(b[..]) == multiset(a[..])
    decreases if next <= dPointer then dPointer - next else next - dPointer
  {
    if b[next] == 'a' {
      next := next + 1;
    } else if b[next] == 'b' {
      b := b[dPointer := b[aPointer]][aPointer := b[next]];
      next := next + 1;
      aPointer := aPointer + 1;
    } else {
      dPointer := dPointer - 1;
      b := b[next := b[dPointer]][dPointer := b[next]];
    }
  }
}
