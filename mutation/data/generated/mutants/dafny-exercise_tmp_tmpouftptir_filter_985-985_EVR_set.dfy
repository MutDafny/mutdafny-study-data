// dafny-exercise_tmp_tmpouftptir_filter.dfy

method Filter(a: seq<char>, b: set<char>) returns (c: set<char>)
  ensures forall x: char {:trigger x in c} {:trigger x in b} {:trigger x in a} :: x in a && x in b <==> x in c
  decreases a, b
{
  var setA: set<char> := set x: char {:trigger x in a} | x in a;
  c := setA * b;
}

method TesterFilter()
{
  var v: set<char> := {'a', 'e', 'i', 'o', 'u'};
  var s: seq<char> := "ant-egg-ink-owl-urn";
  var w: set<char> := Filter(s, v);
  assert w == {'i', 'u', 'a', 'o', 'e'};
  s := "nice-and-easy";
  w := Filter(s, v);
  assert w == {'a', 'e', 'i'};
  s := "mssyysywbrpqsxmnlsghrytx";
  w := Filter(s, v);
  assert w == {};
  s := "iiiiiiiiiiiii";
  w := Filter(s, v);
  assert w == {'i'};
  s := "aeiou";
  w := Filter(s, v);
  assert w == {'a', 'e', 'i', 'o', 'u'};
  s := "u";
  w := Filter(s, v);
  assert w == {'u'};
  s := "f";
  w := Filter(s, v);
  assert w == {};
  s := "";
  w := Filter(s, {});
  assert w == {};
  v := {};
  s := "Any sequence that I like!!!";
  w := Filter(s, v);
  assert w == {};
}
