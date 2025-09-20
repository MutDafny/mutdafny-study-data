// Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula5.dfy

class Set {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, Repr
    decreases Repr + {this}
  {
    this in Repr &&
    store in Repr &&
    0 < store.Length &&
    0 <= nelems <= store.Length &&
    (forall i: int {:trigger store[i]} :: 
      0 <= i < nelems ==>
        store[i] in elems) &&
    forall x: int {:trigger x in elems} :: 
      x in elems ==>
        exists i: int {:trigger store[i]} :: 
          0 <= i < nelems &&
          store[i] == x
  }

  constructor (n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
    decreases n
  {
    store := new int[n];
    Repr := {this, store};
    elems := {};
    nelems := 0;
  }

  function size(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    nelems
  }

  function maxSize(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    store.Length
  }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
    decreases v
  {
    var i := find(v);
    return i >= 0;
  }

  method add(v: int)
    requires RepInv()
    requires size() < maxSize()
    modifies this, Repr
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    decreases v
  {
    var f: int := find(v);
    if f < 0 {
      store[nelems] := v;
      elems := elems + {v};
      assert forall i: int {:trigger store[i]} {:trigger old(store[i])} :: 0 <= i < nelems ==> old(store[i]) == store[i];
      nelems := nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems
    decreases x
  {
    var i: int := 0;
    while i < nelems
      invariant 0 <= i <= nelems
      invariant forall j: int {:trigger store[j]} :: 0 <= j < i ==> x != store[j]
      decreases nelems - i
    {
      if store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  }

  method Main()
  {
    var s := new Set(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  }
}

class PositiveSet {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, Repr
    decreases Repr + {this}
  {
    this in Repr &&
    store in Repr &&
    0 < store.Length &&
    0 <= nelems <= store.Length &&
    (forall i: int {:trigger store[i]} :: 
      0 <= i < nelems ==>
        store[i] in elems) &&
    (forall x: int {:trigger x in elems} :: 
      x in elems ==>
        exists i: int {:trigger store[i]} :: 
          0 <= i < nelems &&
          store[i] == x) &&
    forall x: int {:trigger x in elems} :: 
      x in elems ==>
        x > 0
  }

  constructor (n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
    decreases n
  {
    store := new int[n];
    Repr := {this, store};
    elems := {};
    nelems := 0;
  }

  function size(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    nelems
  }

  function maxSize(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    store.Length
  }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
    decreases v
  {
    var i := find(v);
    return i >= 0;
  }

  method add(v: int)
    requires RepInv()
    requires size() < maxSize()
    modifies this, Repr
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    decreases v
  {
    if v > 0 {
      var f: int := find(v);
      if f < 0 {
        store[nelems] := v;
        elems := elems + {v};
        assert forall i: int {:trigger store[i]} {:trigger old(store[i])} :: 0 <= i < nelems ==> old(store[i]) == store[i];
        nelems := nelems + 1;
      }
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems
    decreases x
  {
    var i: int := 0;
    while i < nelems
      invariant 0 <= i <= nelems
      invariant forall j: int {:trigger store[j]} :: 0 <= j < i ==> x != store[j]
      decreases nelems - i
    {
      if store[i] == x {
        return i;
      }
      i := 0;
    }
    return -1;
  }

  method Main()
  {
    var s := new PositiveSet(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  }
}

class SavingsAccount {
  var cbalance: int
  var sbalance: int
  ghost var Repr: set<object>

  ghost predicate RepInv()
    reads this, Repr
    decreases Repr + {this}
  {
    this in Repr &&
    cbalance >= -sbalance / 2
  }

  ghost predicate PositiveChecking()
    reads this, Repr
    decreases Repr + {this}
  {
    cbalance >= 0
  }

  constructor ()
    ensures fresh(Repr - {this})
    ensures RepInv()
  {
    Repr := {this};
    cbalance := 0;
    sbalance := 0;
  }

  method deposit(amount: int)
    requires amount > 0
    requires RepInv()
    modifies Repr
    ensures RepInv()
    decreases amount
  {
    cbalance := cbalance + amount;
  }

  method withdraw(amount: int)
    requires amount > 0
    requires RepInv()
    modifies Repr
    ensures RepInv()
    decreases amount
  {
    if cbalance - amount >= -sbalance / 2 {
      cbalance := cbalance - amount;
    }
  }

  method save(amount: int)
    requires amount > 0
    requires PositiveChecking()
    requires RepInv()
    modifies Repr
    ensures RepInv()
    decreases amount
  {
    if cbalance >= 0 {
      sbalance := sbalance + amount;
    }
  }

  method rescue(amount: int)
    requires amount > 0
    requires RepInv()
    modifies Repr
    ensures RepInv()
    decreases amount
  {
    if cbalance >= -(sbalance - amount) / 2 {
      sbalance := sbalance - amount;
    }
  }
}

class GrowingSet {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, Repr
    decreases Repr + {this}
  {
    this in Repr &&
    store in Repr &&
    0 < store.Length &&
    0 <= nelems <= store.Length &&
    (forall i: int {:trigger store[i]} :: 
      0 <= i < nelems ==>
        store[i] in elems) &&
    forall x: int {:trigger x in elems} :: 
      x in elems ==>
        exists i: int {:trigger store[i]} :: 
          0 <= i < nelems &&
          store[i] == x
  }

  constructor (n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
    decreases n
  {
    store := new int[n];
    Repr := {this, store};
    elems := {};
    nelems := 0;
  }

  function size(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    nelems
  }

  function maxSize(): int
    requires RepInv()
    reads Repr
    ensures RepInv()
    decreases Repr
  {
    store.Length
  }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
    decreases v
  {
    var i := find(v);
    return i >= 0;
  }

  method add(v: int)
    requires RepInv()
    modifies Repr
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    decreases v
  {
    var f: int := find(v);
    assert forall i: int {:trigger store[i]} {:trigger old(store[i])} :: 0 <= i < nelems ==> old(store[i]) == store[i];
    if f < 0 {
      if nelems == store.Length {
        var tmp := new int[store.Length * 2];
        var i := 0;
        while i < store.Length
          invariant 0 <= i <= store.Length < tmp.Length
          invariant forall j: int {:trigger tmp[j]} {:trigger old(store[j])} :: 0 <= j < i ==> old(store[j]) == tmp[j]
          decreases store.Length - i
          modifies tmp
        {
          tmp[i] := store[i];
          i := i + 1;
        }
        Repr := Repr - {store} + {tmp};
        store := tmp;
      }
      store[nelems] := v;
      elems := elems + {v};
      assert forall i: int {:trigger store[i]} {:trigger old(store[i])} :: 0 <= i < nelems ==> old(store[i]) == store[i];
      nelems := nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems
    decreases x
  {
    var i: int := 0;
    while i < nelems
      invariant 0 <= i <= nelems
      invariant forall j: int {:trigger store[j]} :: 0 <= j < i ==> x != store[j]
      decreases nelems - i
    {
      if store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  }

  method Main()
  {
    var s := new GrowingSet(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  }
}
