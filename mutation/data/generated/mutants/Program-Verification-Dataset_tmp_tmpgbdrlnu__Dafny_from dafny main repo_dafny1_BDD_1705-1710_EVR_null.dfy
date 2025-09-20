// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny1_BDD.dfy


module SimpleBDD {
  class BDDNode {
    static ghost predicate bitfunc(f: map<seq<bool>, bool>, n: nat)
      decreases f, n
    {
      forall i: seq<bool> {:trigger |i|} {:trigger i in f} :: 
        i in f <==> |i| == n
    }

    ghost var Contents: map<seq<bool>, bool>
    ghost var Repr: set<object>
    ghost var n: nat
    var f: BDDNode?
    var t: BDDNode?
    var b: bool

    ghost predicate valid()
      reads this, Repr
      decreases Repr + {this}
    {
      bitfunc(Contents, n) &&
      (0 == n ==>
        (b <==> Contents[[]])) &&
      (0 < n ==>
        this in Repr &&
        f != null &&
        t != null &&
        t in Repr &&
        f in Repr &&
        t.Repr <= Repr &&
        f.Repr <= Repr &&
        this !in f.Repr &&
        this !in t.Repr &&
        t.valid() &&
        f.valid() &&
        t.n == f.n == n - 1 &&
        (forall s: seq<bool> {:trigger t.Contents[s]} {:trigger [true] + s} {:trigger s in t.Contents} | s in t.Contents :: 
          Contents[[true] + s] <==> t.Contents[s]) &&
        forall s: seq<bool> {:trigger f.Contents[s]} {:trigger [false] + s} {:trigger s in f.Contents} | s in f.Contents :: 
          Contents[[false] + s] <==> f.Contents[s])
    }
  }

  class BDD {
    var root: BDDNode

    ghost predicate valid()
      reads this, Repr
      decreases Repr + {this}
    {
      root in Repr &&
      root.Repr <= Repr &&
      root.valid() &&
      n == root.n &&
      Contents == root.Contents
    }

    constructor ()
    {
      root := new BDDNode;
    }

    ghost var Contents: map<seq<bool>, bool>
    var n: nat
    ghost var Repr: set<object>

    method Eval(s: seq<bool>) returns (b: bool)
      requires valid() && |s| == n
      ensures b == Contents[s]
      decreases s
    {
      var node: BDDNode := root;
      var i := n;
      assert s[n - i..] == s;
      while i > 0
        invariant node.valid()
        invariant 0 <= i == node.n <= n
        invariant Contents[s] == node.Contents[s[n - i..]]
        decreases i - 0
      {
        assert s[n - i..] == [s[n - i]] + s[n - i + 1..];
        node := if s[n - i] then null else node.f;
        i := i - 1;
      }
      assert s[n - i..] == [];
      b := node.b;
    }
  }
}
