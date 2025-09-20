// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_c++_maps.dfy

method Test(name: string, b: bool)
  requires b
  decreases name, b
{
  if b {
    print name, ": This is expected\n";
  } else {
    print name, ": This is *** UNEXPECTED *** !!!!\n";
  }
}

method Basic()
{
  var f: map_holder;
  var s: map<uint32, uint32> := map[1 := 0, 2 := 1, 3 := 2, 4 := 3];
  var t: map<uint32, uint32> := map[1 := 0, 2 := 1, 3 := 2, 4 := 3];
  Test("Identity", s == s);
  Test("ValuesIdentity", s == t);
  Test("KeyMembership", 1 in s);
  Test("Value1", s[1] == 0);
  Test("Value2", t[2] == 1);
  var u := s[1 := 42];
  Test("Update Inequality", s != u);
  Test("Update Immutable 1", s == s);
  Test("Update Immutable 2", s[1] == 0);
  Test("Update Result", u[1] == 42);
  Test("Update Others", u[2] == 1);
  var s_keys := s.Keys;
  var t_keys := t.Keys;
  Test("Keys equal", s_keys == t_keys);
  Test("Keys membership 1", 1 in s_keys);
  Test("Keys membership 2", 2 in s_keys);
  Test("Keys membership 3", 3 in s_keys);
  Test("Keys membership 4", 4 in s_keys);
}

method Main()
{
  Basic();
  TestMapMergeSubtraction();
}

method TestMapMergeSubtraction()
{
  TestMapMerge();
  TestMapSubtraction();
  TestNullsAmongKeys();
  TestNullsAmongValues();
}

method TestMapMerge()
{
  var a := map["ronald" := 66 as uint32, "jack" := 70, "bk" := 8];
  var b := map["wendy" := 52, "bk" := 67];
  var ages := a + b;
  assert ages["jack"] == 70;
  assert ages["bk"] == 67;
  assert "sanders" !in ages;
  print |a|, " ", |b|, " ", |ages|, "\n";
  print ages["jack"], " ", ages["wendy"], " ", ages["ronald"], "\n";
  print a["bk"], " ", b["bk"], " ", ages["bk"], "\n";
}

method TestMapSubtraction()
{
  var ages := map["ronald" := 66 as uint32, "jack" := 70, "bk" := 67, "wendy" := 52];
  var d := ages - {};
  var e := ages - {"jack", "sanders"};
  print |ages|, " ", |d|, " ", |e|, "\n";
  print "ronald" in d, " ", "sanders" in d, " ", "jack" in d, " ", "sibylla" in d, "\n";
  print "ronald" in e, " ", "sanders" in e, " ", "jack" in e, " ", "sibylla" in e, "\n";
}

method TestNullsAmongKeys()
{
  var a := new MyClass("ronald");
  var b := new MyClass("wendy");
  var c: MyClass? := null;
  var d := new MyClass("jack");
  var e := new MyClass("sibylla");
  var m := map[a := 0 as uint32, b := 1, c := 2, d := 3];
  var n := map[a := 0, b := 10, c := 20, e := 4];
  var o := map[b := 199, a := 198];
  var o' := map[b := 199, c := 55, a := 198];
  var o'' := map[b := 199, c := 56, a := 198];
  var o3 := map[c := 3, d := 16];
  var x0, x1, x2 := o == o', o' == o'', o' == o';
  print x0, " ", x1, " ", x2, "\n";
  var p := m + n;
  var q := n + o;
  var r := o + m;
  var s := o3 + o;
  var y0, y1, y2, y3 := p == n + m, q == o + q, r == m + o, s == o + o3;
  print y0, " ", y1, " ", y2, " ", y3, "\n";
  print p[a], " ", p[c], " ", p[e], "\n";
  print q[a], " ", q[c], " ", q[e], "\n";
  print r[a], " ", r[c], " ", e in r, "\n";
  p, q, r := GenericMap(m, n, o, a, e);
  print p[a], " ", p[c], " ", p[e], "\n";
  print q[a], " ", q[c], " ", q[e], "\n";
  print r[a], " ", r[c], " ", e in r, "\n";
}

method GenericMap<K, V>(m: map<K, V>, n: map<K, V>, o: map<K, V>, a: K, b: K)
    returns (p: map<K, V>, q: map<K, V>, r: map<K, V>)
  requires a in m.Keys && a in n.Keys
  requires b !in m.Keys && b !in o.Keys
  ensures p == m + n && q == n + o && r == o + m
  decreases m, n, o
{
  p := m + n;
  q := n + o;
  r := o + m;
  print a in m.Keys, " ", a in n.Keys, " ", a in p, " ", b in r, "\n";
  assert p.Keys == m.Keys + n.Keys;
  assert q.Keys == o.Keys + n.Keys;
  assert r.Keys == m.Keys + o.Keys;
}

method TestNullsAmongValues()
{
  var a := new MyClass("ronald");
  var b := new MyClass("wendy");
  var d := new MyClass("jack");
  var e := new MyClass("sibylla");
  var m: map<uint32, MyClass?> := map[0 := a, 1 := b, 2 := null, 3 := null];
  var n: map<uint32, MyClass?> := map[0 := d, 10 := b, 20 := null, 4 := e];
  var o: map<uint32, MyClass?> := map[199 := null, 198 := a];
  var o': map<uint32, MyClass?> := map[199 := b, 55 := null, 198 := a];
  var o'': map<uint32, MyClass?> := map[199 := b, 56 := null, 198 := a];
  var o3: map<uint32, MyClass?> := map[3 := null, 16 := d];
  var x0, x1, x2 := o == o', o' == o'', o' == o';
  print x0, " ", x1, " ", x2, "\n";
  var p := m + n;
  var q := n + o;
  var r := o + m;
  var s := o3 + o;
  var y0, y1, y2, y3 := p == n + m, q == o + n, r == m + o, s == o + o3;
  print y0, " ", y1, " ", y2, " ", y3, "\n";
  print p[0].name, " ", p[1].name, " ", p[20], "\n";
  print q[0].name, " ", q[199], " ", q[20], "\n";
  print r[0].name, " ", r[198].name, " ", 20 in r, "\n";
  p, q, r := GenericMap(m, n, o, 0, 321);
  print p[0].name, " ", p[1].name, " ", p[20], "\n";
  print q[0].name, " ", q[199], " ", q[20], "\n";
  print r[0].name, " ", r[198].name, " ", 20 in r, "\n";
}

newtype uint32 = i: int
  | 0 <= i < 4294967296

datatype map_holder = map_holder(m: map<bool, bool>)

class MyClass {
  const name: string

  constructor (name: string)
    decreases name
  {
    this.name := name;
  }
}
