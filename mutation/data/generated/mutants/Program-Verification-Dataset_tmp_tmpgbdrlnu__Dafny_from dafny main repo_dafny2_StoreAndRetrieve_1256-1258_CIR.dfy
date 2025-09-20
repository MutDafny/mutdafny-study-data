// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_StoreAndRetrieve.dfy


abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      null !in Repr &&
      Valid'()
    }

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}

    constructor Init()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}

    method Store(t: Thing)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}

    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires Valid()
      requires exists t: Thing {:trigger matchCriterion(t)} {:trigger t in Contents} :: t in Contents && matchCriterion(t)
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)

    ghost var Repr: set<object?>
  }
}

abstract module A refines AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> ... {
    constructor Init()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();
    }

    method Store(t: Thing)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      Contents := Contents + {};
      assume Valid'();
    }

    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires Valid()
      requires exists t: Thing {:trigger matchCriterion(t)} {:trigger t in Contents} :: t in Contents && matchCriterion(t)
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var k :| assume k in Contents && matchCriterion(k);
      thing := k;
    }

    ghost var Contents: set<Thing>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      null !in Repr &&
      Valid'()
    }

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}

    ghost var Repr: set<object?>
  }
}

abstract module B refines A {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> ... {
    var arr: seq<Thing>

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}
    {
      Contents == set x: Thing {:trigger x in arr} | x in arr
    }

    constructor Init()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      arr := [];
      Contents := {};
      Repr := {this};
      new;
      assert Valid'();
    }

    method Store(t: Thing)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      arr := arr + [t];
      Contents := Contents + {};
      assert Valid'();
    }

    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires Valid()
      requires exists t: Thing {:trigger matchCriterion(t)} {:trigger t in Contents} :: t in Contents && matchCriterion(t)
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var i := 0;
      while i < |arr|
        invariant i < |arr|
        invariant forall j: int {:trigger arr[j]} :: 0 <= j < i ==> !matchCriterion(arr[j])
        decreases |arr| - i
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      var k := arr[i];
      assert k in Contents && matchCriterion(k);
      thing := k;
      var a: seq<Thing> :| assume Contents == set x: Thing {:trigger x in a} | x in a;
      arr := a;
    }

    ghost var Contents: set<Thing>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      null !in Repr &&
      Valid'()
    }

    ghost var Repr: set<object?>
  }
}

module abC refines B {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> ... {
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires Valid()
      requires exists t: Thing {:trigger matchCriterion(t)} {:trigger t in Contents} :: t in Contents && matchCriterion(t)
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var i := 0;
      while i < |arr|
        invariant i < |arr|
        invariant forall j: int {:trigger arr[j]} :: 0 <= j < i ==> !matchCriterion(arr[j])
        decreases |arr| - i
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      var k := arr[i];
      assert k in Contents && matchCriterion(k);
      thing := k;
      var a := [thing] + arr[..i] + arr[i + 1..];
      assert Contents == set x: Thing {:trigger x in a} | x in a;
      arr := a;
    }

    var arr: seq<Thing>

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}
    {
      Contents == set x: Thing {:trigger x in arr} | x in arr
    }

    constructor Init()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      arr := [];
      Contents := {};
      Repr := {this};
      new;
      assert Valid'();
    }

    method Store(t: Thing)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      arr := arr + [t];
      Contents := Contents + {};
      assert Valid'();
    }

    ghost var Contents: set<Thing>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      null !in Repr &&
      Valid'()
    }

    ghost var Repr: set<object?>
  }
}

abstract module AbstractClient {
  method Test()
  {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := (r: real) => true;
    var r := s.Retrieve(fn);
    print r, "\n";
  }

  import S : AbstractInterface
}

module Client refines AbstractClient {
  method Main()
  {
    Test();
  }

  method Test()
  {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := (r: real) => true;
    var r := s.Retrieve(fn);
    print r, "\n";
  }

  import S = abC
}
