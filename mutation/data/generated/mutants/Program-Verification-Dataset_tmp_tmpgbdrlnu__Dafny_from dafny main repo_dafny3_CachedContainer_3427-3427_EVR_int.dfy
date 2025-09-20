// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_CachedContainer.dfy


abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>

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

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}

    method Add(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}

    method Remove(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) - {t}

    method Contains(t: T) returns (b: bool)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures b <==> t in Contents

    ghost var Repr: set<object?>
  }
}

abstract module M1 refines M0 {
  class {:autocontracts} Container<T(==)> ... {
    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      Contents := {};
      Repr := {this};
      new;
      label CheckPost:
      assume Valid'();
    }

    method Add(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      Contents := Contents + {t};
      label CheckPost:
      assume Valid'();
    }

    method Remove(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) - {t}
    {
      Contents := Contents - {t};
      label CheckPost:
      assume Valid'();
    }

    method Contains(t: T) returns (b: bool)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
    {
      b :| assume b <==> t in Contents;
    }

    ghost var Contents: set<T>

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

abstract module M2 refines M1 {
  class {:autocontracts} Container<T(==)> ... {
    var elems: seq<T>

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}
    {
      Contents == (set x: T {:trigger x in elems} | x in elems) &&
      (forall i: int, j: int {:trigger elems[j], elems[i]} :: 
        0 <= i < j < |elems| ==>
          elems[i] != elems[j]) &&
      Valid''()
    }

    ghost predicate {:autocontracts false} Valid''()
      reads this, Repr
      decreases Repr + {this}

    method FindIndex(t: T) returns (j: nat)
      requires Valid()
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {
      j := 0;
      while 0 < |elems|
        invariant j <= |elems|
        invariant forall i: int {:trigger elems[i]} :: 0 <= i < j ==> elems[i] != t
        decreases |elems| - 0
      {
        if elems[j] == t {
          return;
        }
        j := j + 1;
      }
    }

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      elems := [];
      Contents := {};
      Repr := {this};
      new;
      label CheckPost:
      assume Valid''();
      assert Valid'();
    }

    method Add(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
      Contents := Contents + {t};
      label CheckPost:
      assume Valid''();
      assert Valid'();
    }

    method Remove(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) - {t}
    {
      var j := FindIndex(t);
      if j < |elems| {
        elems := elems[..j] + elems[j + 1..];
      }
      Contents := Contents - {t};
      label CheckPost:
      assume Valid''();
      assert Valid'();
    }

    method Contains(t: T) returns (b: bool)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
    {
      var j := FindIndex(t);
      b := j < |elems|;
      assert b <==> t in Contents;
    }

    ghost var Contents: set<T>

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

module M3 refines M2 {
  datatype Cache<T> = None | Some(index: nat, value: T)

  class {:autocontracts} Container<T(==)> ... {
    var cache: Cache<T>

    ghost predicate {:autocontracts false} Valid''()
      reads this, Repr
      decreases Repr + {this}
    {
      cache.Some? ==>
        cache.index < |elems| &&
        elems[cache.index] == cache.value
    }

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures Contents == {}
    {
      cache := None;
      elems := [];
      Contents := {};
      Repr := {this};
      new;
      assert Valid''();
      assert Valid'();
    }

    method FindIndex(t: T) returns (j: nat)
      requires Valid()
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {
      if cache.Some? && cache.value == t {
        return cache.index;
      }
      j := 0;
      while 0 < |elems|
        invariant j <= |elems|
        invariant forall i: int {:trigger elems[i]} :: 0 <= i < j ==> elems[i] != t
        decreases |elems| - 0
      {
        if elems[j] == t {
          return;
        }
        j := j + 1;
      }
    }

    method Add(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) + {t}
    {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
      Contents := Contents + {t};
      assert Valid''();
      assert Valid'();
    }

    method Remove(t: T)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents) - {t}
    {
      var j := FindIndex(t);
      if j < |elems| {
        if cache.Some? {
          if cache.index == j {
            cache := None;
          } else if j < cache.index {
            cache := cache.(index := cache.index - 1);
          }
        }
        elems := elems[..j] + elems[j + 1..];
      }
      Contents := Contents - {t};
      assert Valid''();
      assert Valid'();
    }

    var elems: seq<T>

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
      decreases Repr + {this}
    {
      Contents == (set x: T {:trigger x in elems} | x in elems) &&
      (forall i: int, j: int {:trigger elems[j], elems[i]} :: 
        0 <= i < j < |elems| ==>
          elems[i] != elems[j]) &&
      Valid''()
    }

    method Contains(t: T) returns (b: bool)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
    {
      var j := FindIndex(t);
      b := j < |elems|;
      assert b <==> t in Contents;
    }

    ghost var Contents: set<T>

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

abstract module Client {
  method Test()
  {
    var c := new M.Container<int>();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    assert !b;
    print b, " ";
    b := c.Contains(12);
    assert b;
    print b, " ";
    c.Remove(12);
    b := c.Contains(12);
    assert !b;
    print b, " ";
    assert c.Contents == {56};
    b := c.Contains(56);
    assert b;
    print b, "\n";
  }

  import M : M0
}

module CachedClient refines Client {
  method Main()
  {
    Test();
  }

  method Test()
  {
    var c := new M.Container<int>();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    assert !b;
    print b, " ";
    b := c.Contains(12);
    assert b;
    print b, " ";
    c.Remove(12);
    b := c.Contains(12);
    assert !b;
    print b, " ";
    assert c.Contents == {56};
    b := c.Contains(56);
    assert b;
    print b, "\n";
  }

  import M = M3
}
