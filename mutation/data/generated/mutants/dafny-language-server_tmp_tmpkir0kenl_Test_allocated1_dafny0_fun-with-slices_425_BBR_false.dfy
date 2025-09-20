// dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices.dfy

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
  decreases s, a, index
{
  var i := index;
  while false
    invariant index <= i <= index + |s| <= a.Length
    invariant a[..] == old(a[..index]) + s[..i - index] + old(a[i..])
  {
    label A:
    a[i] := s[i - index];
    calc {
      a[..];
    ==
      old@A(a[..])[i := s[i - index]];
    ==
      (old(a[..index]) + s[..i - index] + old(a[i..]))[i := s[i - index]];
    ==
      {
        assert old(a[..index]) + s[..i - index] + old(a[i..]) == old(a[..index]) + s[..i - index] + old(a[i..]);
      }
      (old(a[..index]) + s[..i - index] + old(a[i..]))[i := s[i - index]];
    ==
      {
        assert |old(a[..index]) + s[..i - index]| == i;
      }
      old(a[..index]) + s[..i - index] + old(a[i..])[0 := s[i - index]];
    ==
      {
        assert old(a[i..])[0 := s[i - index]] == [s[i - index]] + old(a[i..])[1..];
      }
      old(a[..index]) + s[..i - index] + [s[i - index]] + old(a[i..])[1..];
    ==
      {
        assert old(a[i..])[1..] == old(a[i + 1..]);
      }
      old(a[..index]) + s[..i - index] + [s[i - index]] + old(a[i + 1..]);
    ==
      old(a[..index]) + (s[..i - index] + [s[i - index]]) + old(a[i + 1..]);
    ==
      {
        assert s[..i - index] + [s[i - index]] == s[..i + 1 - index];
      }
      old(a[..index]) + s[..i + 1 - index] + old(a[i + 1..]);
    }
    i := i + 1;
  }
}
