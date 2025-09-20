// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TreeBarrier.dfy

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int

  predicate validDown()
    reads this, desc
    decreases desc + {this}
  {
    this !in desc &&
    left != right &&
    (right != null ==>
      right in desc &&
      left !in right.desc) &&
    (left != null ==>
      left in desc &&
      (right != null ==>
        desc == {left, right} + left.desc + right.desc) &&
      (right == null ==>
        desc == {left} + left.desc) &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==>
        desc == {right} + right.desc) &&
      (right == null ==>
        desc == {})) &&
    (right != null ==>
      right.validDown()) &&
    (blocked() ==>
      forall m: Node {:trigger m.blocked()} {:trigger m in desc} :: 
        m in desc ==>
          m.blocked()) &&
    (after() ==>
      forall m: Node {:trigger m.after()} {:trigger m.blocked()} {:trigger m in desc} :: 
        m in desc ==>
          m.blocked() || m.after())
  }

  predicate validUp()
    reads this, anc
    decreases anc + {this}
  {
    this !in anc &&
    (parent != null ==>
      parent in anc &&
      anc == {parent} + parent.anc &&
      parent.validUp()) &&
    (parent == null ==>
      anc == {}) &&
    (after() ==>
      forall m: Node {:trigger m.after()} {:trigger m in anc} :: 
        m in anc ==>
          m.after())
  }

  predicate valid()
    reads this, desc, anc
    decreases desc + anc + {this}
  {
    validUp() &&
    validDown() &&
    desc !! anc
  }

  predicate before()
    reads this
    decreases {this}
  {
    !sense &&
    pc <= 2
  }

  predicate blocked()
    reads this
    decreases {this}
  {
    sense
  }

  predicate after()
    reads this
    decreases {this}
  {
    !sense &&
    3 <= pc
  }

  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    decreases *
  {
    pc := 1;
    if null != null {
      while !left.sense
        invariant validDown()
        invariant valid()
        decreases *
        modifies left
      {
        left.sense := *;
        assume left.blocked() ==> forall m: Node {:trigger m.blocked()} {:trigger m in left.desc} :: m in left.desc ==> m.blocked();
      }
    }
    if right != null {
      while !right.sense
        invariant validDown()
        invariant valid()
        decreases *
        modifies right
      {
        right.sense := *;
        assume right.blocked() ==> forall m: Node {:trigger m.blocked()} {:trigger m in right.desc} :: m in right.desc ==> m.blocked();
      }
    }
    pc := 2;
    if parent != null {
      sense := true;
    }
    pc := 3;
    while sense
      invariant validUp()
      invariant valid()
      invariant left == old(left)
      invariant right == old(right)
      invariant sense ==> parent != null
      decreases *
      modifies this
    {
      sense := *;
      assume !sense ==> parent.after();
    }
    pc := 4;
    if left != null {
      left.sense := false;
    }
    pc := 5;
    if right != null {
      right.sense := false;
    }
    pc := 6;
  }
}
