// DafnyPrograms_tmp_tmp74_f9k_c_map-multiset-implementation.dfy

trait MyMultiset {
  ghost predicate Valid()
    reads this
    decreases {this}

  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    requires Valid()
    modifies this
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange
    decreases elem

  ghost predicate Contains(elem: int)
    reads this
    decreases {this}, elem
  {
    elem in theMultiset
  }

  method Remove(elem: int) returns (didChange: bool)
    requires Valid()
    modifies this
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    ensures !old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures !old(Contains(elem)) ==> !didChange
    decreases elem

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
    decreases other

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

class MultisetImplementationWithMap extends MyMultiset {
  ghost predicate Valid()
    reads this
    decreases {this}
  {
    (forall i: int {:trigger elements[i]} {:trigger i in elements.Keys} | i in elements.Keys :: 
      elements[i] > 0) &&
    theMultiset == A(elements) &&
    forall i: int {:trigger Contains(i)} {:trigger i in elements.Keys} :: 
      i in elements.Keys <==> Contains(i)
  }

  function A(m: map<int, nat>): (s: multiset<int>)
    ensures (forall i: int {:trigger A(m)[i]} {:trigger m[i]} {:trigger i in m} | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && forall i: int {:trigger A(m)[i]} {:trigger i in m} :: i in m <==> i in A(m)
    decreases m

  lemma LemmaReverseA(m: map<int, nat>, s: seq<int>)
    requires (forall i: int {:trigger multiset(s)[i]} {:trigger m[i]} {:trigger i in m} | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)
    decreases m, s

  var elements: map<int, nat>

  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {
    elements := map[];
    theMultiset := multiset{};
  }

  method Add(elem: int) returns (didChange: bool)
    requires Valid()
    modifies this
    ensures elem in elements ==> elements == elements[elem := elements[elem]]
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures !(elem in elements) ==> elements == elements[elem := 1]
    ensures didChange
    ensures Contains(elem)
    ensures Valid()
    decreases elem
  {
    if !(elem in elements) {
      elements := elements[elem := 1];
    } else {
      elements := map[][elem := elements[elem] + 1];
    }
    didChange := true;
    theMultiset := A(elements);
  }

  method Remove(elem: int) returns (didChange: bool)
    requires Valid()
    modifies this
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    ensures !old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures !old(Contains(elem)) ==> !didChange
    ensures didChange <==> elements != old(elements)
    decreases elem
  {
    if elem !in elements {
      assert !Contains(elem);
      assert theMultiset == old(theMultiset);
      assert Valid();
      return false;
    }
    assert Contains(elem);
    elements := elements[elem := elements[elem] - 1];
    if elements[elem] == 0 {
      elements := elements - {elem};
    }
    theMultiset := A(elements);
    didChange := true;
  }

  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {
    var result := Map2Seq(elements);
    return |result|;
  }

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
    decreases other
  {
    var otherMapSeq := other.getElems();
    assert multiset(otherMapSeq) == other.theMultiset;
    var c := this.getElems();
    return multiset(c) == multiset(otherMapSeq);
  }

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {
    var result: seq<int>;
    result := Map2Seq(elements);
    return result;
  }

  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i: int {:trigger m[i]} {:trigger i in m.Keys} | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i: int {:trigger m[i]} {:trigger multiset(s)[i]} {:trigger i in m.Keys} | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i: int {:trigger i in s} {:trigger i in m.Keys} | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i: int {:trigger multiset(s)[i]} {:trigger m[i]} {:trigger i in m} | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    decreases m
  {
    if |m| == 0 {
      return [];
    }
    var keys := m.Keys;
    var key: int;
    s := [];
    while keys != {}
      invariant forall i: int {:trigger multiset(s)[i]} {:trigger i in keys} {:trigger i in m.Keys} | i in m.Keys :: i in keys <==> multiset(s)[i] == 0
      invariant forall i: int {:trigger m[i]} {:trigger multiset(s)[i]} {:trigger i in m.Keys - keys} | i in m.Keys - keys :: multiset(s)[i] == m[i]
      decreases keys
    {
      key :| key in keys;
      var counter := 0;
      while counter < m[key]
        invariant 0 <= counter <= m[key]
        invariant multiset(s)[key] == counter
        invariant forall i: int {:trigger multiset(s)[i]} {:trigger i in keys} {:trigger i in m.Keys} | i in m.Keys && i != key :: i in keys <==> multiset(s)[i] == 0
        invariant forall i: int {:trigger m[i]} {:trigger multiset(s)[i]} {:trigger i in m.Keys - keys} | i in m.Keys - keys :: multiset(s)[i] == m[i]
        decreases m[key] - counter
      {
        s := s + [key];
        counter := counter + 1;
      }
      keys := keys - {key};
    }
    LemmaReverseA(m, s);
  }

  method Test1()
    modifies this
  {
    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();
    var a := this.getElems();
    assert multiset(a) == multiset{1, 2, 3, 4};
    var theOtherBag: MultisetImplementationWithMap;
    theOtherBag := new MultisetImplementationWithMap.MultisetImplementationWithMap();
    var b := this.equals(theOtherBag);
    assert b == false;
    theOtherBag.theMultiset := multiset{1, 2, 3, 4};
    theOtherBag.elements := map[1 := 1, 2 := 1, 3 := 1, 4 := 1];
    var c := this.equals(theOtherBag);
    assert c == true;
  }

  method Test2()
    modifies this
  {
    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();
    var a := this.getElems();
    assert multiset(a) == multiset{1, 2, 3, 4};
    var d := this.Add(3);
    var e := this.getElems();
    assert multiset(e) == multiset([1, 2, 3, 4, 3]);
    var f := this.Remove(4);
    var g := this.getElems();
    assert multiset(g) == multiset([1, 2, 3, 3]);
    var h := this.Length();
    assert h == 4;
  }

  method Test3()
  {
    var m := map[2 := 2, 3 := 3, 4 := 4];
    var s: seq<int> := [2, 2, 3, 3, 3, 4, 4, 4, 4];
    var a := this.Map2Seq(m);
    assert multiset(a) == multiset(s);
    var x := map[1 := 1, 2 := 1, 3 := 1];
    var y: seq<int> := [1, 2, 3];
    var z := this.Map2Seq(x);
    assert multiset(z) == multiset(y);
  }
}
