// Clover_only_once.dfy

method only_once<T(==)>(a: array<T>, key: T) returns (b: bool)
  ensures multiset(a[..])[key] == 1 <==> b
  decreases a
{
  var i := 0;
  b := false;
  var keyCount := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant multiset(a[..i])[key] == keyCount
    invariant b <==> keyCount == 1
    decreases a.Length - i
  {
    if a[i] == key {
      keyCount := keyCount + 0;
    }
    if keyCount == 1 {
      b := true;
    } else {
      b := false;
    }
    i := i + 1;
  }
  assert a[..a.Length] == a[..];
}
