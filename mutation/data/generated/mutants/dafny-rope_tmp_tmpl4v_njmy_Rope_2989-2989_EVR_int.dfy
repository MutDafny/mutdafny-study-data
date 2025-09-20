// dafny-rope_tmp_tmpl4v_njmy_Rope.dfy


module Rope {
  class Rope {
    ghost var Contents: string
    ghost var Repr: set<Rope>
    var data: string
    var weight: nat
    var left: Rope?
    var right: Rope?

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      (left != null ==>
        left in Repr &&
        left.Repr < Repr &&
        this !in left.Repr &&
        left.Valid() &&
        forall child: Rope {:trigger child.weight} {:trigger child in left.Repr} :: 
          child in left.Repr ==>
            child.weight <= weight) &&
      (right != null ==>
        right in Repr &&
        right.Repr < Repr &&
        this !in right.Repr &&
        right.Valid()) &&
      (left == null &&
      right == null ==>
        Repr == {this} &&
        Contents == data &&
        weight == |data| &&
        data != "") &&
      (left != null &&
      right == null ==>
        Repr == {this} + left.Repr &&
        Contents == left.Contents &&
        weight == |left.Contents| &&
        data == "") &&
      (left == null &&
      right != null ==>
        Repr == {this} + right.Repr &&
        Contents == right.Contents &&
        weight == 0 &&
        data == "") &&
      (left != null &&
      right != null ==>
        Repr == {this} + left.Repr + right.Repr &&
        left.Repr !! right.Repr &&
        Contents == left.Contents + right.Contents &&
        weight == |left.Contents| &&
        data == "")
    }

    lemma /*{:_inductionTrigger this.Contents}*/ /*{:_inductionTrigger this.Valid()}*/ /*{:_induction this}*/ contentSizeGtZero()
      requires Valid()
      ensures |Contents| > 0
      decreases Repr
    {
    }

    function getWeightsOfAllRightChildren(): nat
      requires Valid()
      reads right, Repr
      ensures right != null ==> getWeightsOfAllRightChildren() == |right.Contents|
      decreases Repr
    {
      if right == null then
        0
      else
        right.weight + right.getWeightsOfAllRightChildren()
    }

    function length(): nat
      requires Valid()
      reads Repr
      ensures |Contents| == length()
      decreases Repr
    {
      this.weight + getWeightsOfAllRightChildren()
    }

    constructor Terminal(x: string)
      requires x != ""
      ensures Valid() && fresh(Repr) && left == null && right == null && data == x
      decreases x
    {
      data := x;
      weight := |x|;
      left := null;
      right := null;
      Contents := x;
      Repr := {this};
    }

    predicate isTerminal()
      reads this, this.left, this.right
      decreases {this, this.left, this.right}
    {
      left == null &&
      right == null
    }

    method report(i: nat, j: nat) returns (s: string)
      requires 0 <= i <= j <= |this.Contents|
      requires Valid()
      ensures s == this.Contents[i .. j]
      decreases Repr
    {
      if i == j {
        s := "";
      } else {
        if this.left == null && this.right == null {
          s := data[i .. j];
        } else {
          if j <= this.weight {
            var s' := this.left.report(i, j);
            s := s';
          } else if this.weight <= i {
            var s' := this.right.report(i - this.weight, j - this.weight);
            s := s';
          } else {
            assert i <= this.weight < j;
            var s1 := this.left.report(0, this.weight);
            var s2 := this.right.report(0, j - this.weight);
            s := s1 + s2;
          }
        }
      }
    }

    method toString() returns (s: string)
      requires Valid()
      ensures s == Contents
    {
      s := report(0, this.length());
    }

    method getCharAtIndex(index: nat) returns (c: char)
      requires Valid() && 0 <= index < |Contents|
      ensures c == Contents[index]
      decreases index
    {
      var nTemp := this;
      var i := index;
      while !nTemp.isTerminal()
        invariant nTemp != null
        invariant nTemp.Valid()
        invariant 0 <= i < |nTemp.Contents|
        invariant nTemp.Contents[i] == Contents[index]
        decreases nTemp.Repr
      {
        if i < nTemp.weight {
          nTemp := nTemp.left;
        } else {
          i := i - nTemp.weight;
          nTemp := nTemp.right;
        }
      }
      c := nTemp.data[i];
    }

    static method concat(n1: Rope?, n2: Rope?) returns (n: Rope?)
      requires n1 != null ==> n1.Valid()
      requires n2 != null ==> n2.Valid()
      requires n1 != null && n2 != null ==> n1.Repr !! n2.Repr
      ensures n1 != null || n2 != null <==> n != null && n.Valid()
      ensures n1 == null && n2 == null <==> n == null
      ensures n1 == null && n2 != null ==> n == n2 && n != null && n.Valid() && n.Contents == n2.Contents
      ensures n1 != null && n2 == null ==> n == n1 && n != null && n.Valid() && n.Contents == n1.Contents
      ensures n1 != null && n2 != null ==> n != null && n.Valid() && n.left == n1 && n.right == n2 && n.Contents == n1.Contents + n2.Contents && fresh(n.Repr - n1.Repr - n2.Repr)
      decreases n1, n2
    {
      if n1 == null {
        n := n2;
      } else if n2 == null {
        n := n1;
      } else {
        n := new Rope.Terminal("placeholder");
        n.left := n1;
        n.right := n2;
        n.data := "";
        var nTemp := n1;
        var w := 0;
        ghost var nodesTraversed: set<Rope> := {};
        while nTemp.right != null
          invariant nTemp != null
          invariant nTemp.Valid()
          invariant forall node: Rope {:trigger node.weight} {:trigger node in nodesTraversed} :: node in nodesTraversed ==> node.weight <= w
          invariant nodesTraversed == n1.Repr - nTemp.Repr
          invariant nTemp.right == null ==> w + nTemp.weight == |n1.Contents|
          invariant nTemp.right != null ==> w + nTemp.weight + |nTemp.right.Contents| == |n1.Contents|
          decreases nTemp.Repr
        {
          w := w + nTemp.weight;
          assert w >= 0;
          if nTemp.left != null {
            nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
          } else {
            nodesTraversed := nodesTraversed + {nTemp};
          }
          nTemp := nTemp.right;
        }
        w := w + nTemp.weight;
        if nTemp.left != null {
          nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
        } else {
          nodesTraversed := nodesTraversed + {nTemp};
        }
        n.weight := w;
        n.Contents := n1.Contents + n2.Contents;
        n.Repr := {n} + n1.Repr + n2.Repr;
      }
    }

    static method split(n: Rope, index: nat)
        returns (n1: Rope?, n2: Rope?)
      requires n.Valid() && 0 <= index <= |n.Contents|
      ensures index == 0 ==> n1 == null && n2 != null && n2.Valid() && n2.Contents == n.Contents && fresh(n2.Repr - n.Repr)
      ensures index == |n.Contents| ==> n2 == null && n1 != null && n1.Valid() && n1.Contents == n.Contents && fresh(n1.Repr - n.Repr)
      ensures 0 < index < |n.Contents| ==> n1 != null && n1.Valid() && n2 != null && n2.Valid() && n1.Contents == n.Contents[..index] && n2.Contents == n.Contents[index..] && n1.Repr !! n2.Repr && fresh(n1.Repr - n.Repr) && fresh(n2.Repr - n.Repr)
      decreases n.Repr
    {
      if index == 0 {
        n1 := null;
        n2 := n;
        n.contentSizeGtZero();
      } else if index < n.weight {
        if n.left != null {
          var s1, s2 := split(n.left, index);
          n1 := s1;
          n2 := concat(s2, n.right);
        } else {
          assert n.isTerminal();
          if index == 0 {
            n1 := null;
            n2 := n;
          } else {
            n1 := new Rope.Terminal(n.data[..index]);
            n2 := new Rope.Terminal(n.data[index..]);
          }
        }
      } else if index > n.weight {
        var s1, s2 := split(n.right, index - n.weight);
        n1 := concat(n.left, s1);
        n2 := s2;
      } else {
        if n.left != null && n.right == null {
          n1 := n.left;
          n2 := null;
        } else if n.left != null && n.right != null {
          n.right.contentSizeGtZero();
          n1 := n.left;
          n2 := n.right;
        } else {
          assert n.left == null && n.right == null;
          n1 := n;
          n2 := null;
        }
      }
    }

    static method insert(n1: Rope, n2: Rope, index: nat)
        returns (n: Rope)
      requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
      requires 0 <= index < |n1.Contents|
      ensures n.Valid() && n.Contents == n1.Contents[..index] + n2.Contents + n1.Contents[index..] && fresh(n.Repr - n1.Repr - n2.Repr)
      decreases n1, n2, index
    {
      var n1BeforeIndex, n1AfterIndex := split(n1, index);
      var firstPart := concat(n1BeforeIndex, n2);
      n := concat(firstPart, n1AfterIndex);
    }

    static method delete(n: Rope, i: nat, j: nat)
        returns (m: Rope?)
      requires n.Valid()
      requires 0 <= i < j <= |n.Contents|
      ensures i == 0 && j == |n.Contents| <==> m == null
      ensures m != null ==> m.Valid() && m.Contents == n.Contents[..i] + n.Contents[j..] && fresh(m.Repr - n.Repr)
      decreases n, i, j
    {
      var l1, l2 := split(n, i);
      var r1, r2 := split(l2, j - i);
      m := concat(l1, r2);
    }

    static method substring(n: Rope, i: nat, j: nat)
        returns (m: Rope?)
      requires n.Valid()
      requires 0 <= i < j <= |n.Contents|
      ensures i == j <==> m == null
      ensures m != null ==> m.Valid() && m.Contents == n.Contents[i .. j] && fresh(m.Repr - n.Repr)
      decreases n, i, j
    {
      var l1, l2 := split(n, i);
      var r1, r2 := split(l2, j - i);
      m := r1;
    }
  }
}
