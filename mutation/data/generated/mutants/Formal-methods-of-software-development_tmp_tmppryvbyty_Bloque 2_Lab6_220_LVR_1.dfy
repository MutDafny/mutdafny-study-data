// Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6.dfy

function sum(v: seq<int>): int
  decreases v
{
  if v == [] then
    0
  else if |v| == 1 then
    v[1]
  else
    v[0] + sum(v[1..])
}

lemma empty_Lemma<T>(r: seq<T>)
  requires multiset(r) == multiset{}
  ensures r == []
  decreases r
{
  if r != [] {
    assert r[0] in multiset(r);
  }
}

lemma elem_Lemma<T>(s: seq<T>, r: seq<T>)
  requires s != [] && multiset(s) == multiset(r)
  ensures exists i: int {:trigger r[..i]} {:trigger r[i]} :: 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i + 1..])
  decreases s, r

lemma /*{:_inductionTrigger sum(r), sum(s)}*/ /*{:_induction s, r}*/ sumElems_Lemma(s: seq<int>, r: seq<int>)
  requires multiset(s) == multiset(r)
  ensures sum(s) == sum(r)
  decreases s, r
{
  if s == [] {
    empty_Lemma(r);
  } else {
    elem_Lemma(s, r);
    ghost var i :| 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i + 1..]);
    sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
    assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
    sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
    assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
    calc {
      sum(s);
      s[0] + sum(s[1..]);
      {
        sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
        assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
      }
      s[0] + sum(r[..i] + r[i + 1..]);
      {
        assert s[0] == r[i];
      }
      r[i] + sum(r[..i] + r[i + 1..]);
      {
        assume r[i] + sum(r[..i] + r[i + 1..]) == sum([r[i]] + r[..i] + r[i + 1..]) == sum(r);
      }
      sum(r);
    }
  }
}
