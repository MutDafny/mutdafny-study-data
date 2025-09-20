// dafny_examples_tmp_tmp8qotd4ez_test_shuffle.dfy

method random(a: int, b: int) returns (r: int)
  ensures a <= b ==> a <= r <= b
  decreases a, b

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures t in s1 <==> t in s2
  decreases s1, s2
{
  calc <==> {
    t in s1;
    t in multiset(s1);
  }
}

lemma eqMultiset<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures forall t: T {:trigger t in s2} {:trigger t in s1} :: t in s1 <==> t in s2
  decreases s1, s2
{
  forall t: T | true {
    eqMultiset_t(t, s1, s2);
  }
}

method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m: int {:trigger old(a[m])} {:trigger a[m]} :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
  decreases a, i, j
{
  var t := a[i];
  a[i] := a[j];
}

method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
  ensures result.Length == m_dataEntries.Length
  ensures multiset(result[..]) == multiset(m_dataEntries[..])
  decreases m_dataEntries
{
  result := new T[m_dataEntries.Length];
  forall i: int | 0 <= i < m_dataEntries.Length {
    result[i] := m_dataEntries[i];
  }
  assert result[..] == m_dataEntries[..];
  var k := result.Length - 1;
  while k >= 0
    invariant multiset(result[..]) == multiset(m_dataEntries[..])
    decreases k - 0
  {
    var i := random(0, k);
    assert i >= 0 && i <= k;
    if i != k {
      swap(result, i, k);
    }
    k := k - 1;
  }
}

function set_of_seq<T>(s: seq<T>): set<T>
  decreases s
{
  set x: T {:trigger x in s} | x in s :: x
}

lemma in_set_of_seq<T>(x: T, s: seq<T>)
  ensures x in s <==> x in set_of_seq(s)
  decreases s

lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  requires set_of_seq(s1) <= set_of_seq(s2)
  ensures forall x: T {:trigger x in s2} {:trigger x in s1} :: x in s1 ==> x in s2
  decreases s1, s2

method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
  decreases m_workList, avoidSet
{
  var k := m_workList.Length - 1;
  while k >= 0
    decreases k - 0
  {
    var i := random(0, k);
    assert i >= 0 && i <= k;
    e := m_workList[i];
    if e !in avoidSet {
      return e;
    }
    k := k - 1;
  }
  return m_workList[0];
}
