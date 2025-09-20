// dafny-language-server_tmp_tmpkir0kenl_Test_vacid0_Composite.dfy

method Main()
{
  var c0 := new Composite.Init(57);
  var c1 := new Composite.Init(12);
  c0.Add({c0}, c1, {c1});
  var c2 := new Composite.Init(48);
  var c3 := new Composite.Init(48);
  c2.Add({c2}, c3, {c3});
  c0.Add({c0, c1}, c2, {c2, c3});
  ghost var S := {c0, c1, c2, c3};
  c1.Update(100, S);
  c2.Update(102, S);
  c2.Dislodge(S);
  c2.Update(496, S);
  c0.Update(0, S);
}

method Harness()
{
  var a := new Composite.Init(5);
  var b := new Composite.Init(7);
  a.Add({a}, b, {b});
  assert a.sum == 12;
  b.Update(17, {a, b});
  assert a.sum == 22;
  var c := new Composite.Init(10);
  b.Add({a, b}, c, {c});
  b.Dislodge({a, b, c});
  assert b.sum == 27;
}

class Composite {
  var left: Composite?
  var right: Composite?
  var parent: Composite?
  var val: int
  var sum: int

  function Valid(S: set<Composite>): bool
    reads this, parent, left, right
    decreases {this, parent, left, right}, S
  {
    this in S &&
    (parent != null ==>
      parent in S &&
      (parent.left == this || parent.right == this)) &&
    (left != null ==>
      left in S &&
      left.parent == this &&
      left != right) &&
    (right != null ==>
      right in S &&
      right.parent == this &&
      left != right) &&
    sum == val + (if left == null then 0 else left.sum) + if right == null then 0 else right.sum
  }

  function Acyclic(S: set<Composite>): bool
    reads S
    decreases S, S
  {
    this in S &&
    (parent != null ==>
      parent.Acyclic(S - {this}))
  }

  method Init(x: int)
    modifies this
    ensures Valid({this}) && Acyclic({this}) && val == x && parent == null
    decreases x
  {
    parent := null;
    left := null;
    right := null;
    val := x;
    sum := val;
  }

  method Update(x: int, ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    ensures forall c: Composite {:trigger old(c.parent)} {:trigger c.parent} {:trigger old(c.right)} {:trigger c.right} {:trigger old(c.left)} {:trigger c.left} {:trigger c in S} :: (c in S ==> c.left == old(c.left)) && (c in S ==> c.right == old(c.right)) && (c in S ==> c.parent == old(c.parent))
    ensures forall c: Composite {:trigger old(c.val)} {:trigger c.val} {:trigger c in S} :: c in S && c != this ==> c.val == old(c.val)
    ensures val == x
    decreases x, S
  {
    var delta := x - val;
    val := x;
  }

  method Add(ghost S: set<Composite>, child: Composite, ghost U: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    requires child in U
    requires forall c: Composite {:trigger c.Valid(U)} {:trigger c in U} :: c in U ==> c.Valid(U)
    requires S !! U
    requires left == null || right == null
    requires child.parent == null
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c: Composite {:trigger old(c.right)} {:trigger c.right} {:trigger old(c.left)} {:trigger c.left} {:trigger c in S} :: (c in S && c != this ==> c.left == old(c.left)) && (c in S && c != this ==> c.right == old(c.right))
    ensures old(left) != null ==> left == old(left)
    ensures old(right) != null ==> right == old(right)
    ensures forall c: Composite {:trigger old(c.val)} {:trigger c.val} {:trigger old(c.parent)} {:trigger c.parent} {:trigger c in S} :: (c in S ==> c.parent == old(c.parent)) && (c in S ==> c.val == old(c.val))
    ensures child.parent == this
    ensures forall c: Composite {:autotriggers false} :: c in S + U ==> c.Valid(S + U)
    decreases S, child, U
  {
    if left == null {
      left := child;
    } else {
      right := child;
    }
    child.parent := this;
    Adjust(child.sum, S, S + U);
  }

  method Dislodge(ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    ensures forall c: Composite {:trigger old(c.val)} {:trigger c.val} {:trigger c in S} :: c in S ==> c.val == old(c.val)
    ensures forall c: Composite {:trigger old(c.parent)} {:trigger c.parent} {:trigger c in S} :: c in S && c != this ==> c.parent == old(c.parent)
    ensures parent == null
    ensures forall c: Composite {:trigger old(c.left)} {:trigger c.left} {:trigger c in S} :: c in S ==> c.left == old(c.left) || (old(c.left) == this && c.left == null)
    ensures forall c: Composite {:trigger old(c.right)} {:trigger c.right} {:trigger c in S} :: c in S ==> c.right == old(c.right) || (old(c.right) == this && c.right == null)
    ensures Acyclic({this})
    decreases S
  {
    var p := parent;
    parent := null;
    if p != null {
      if p.left == this {
        p.left := null;
      } else {
        p.right := null;
      }
      var delta := -sum;
      p.Adjust(delta, S - {this}, S);
    }
  }

  method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && Acyclic(U)
    requires forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S && c != this ==> c.Valid(S)
    requires parent != null ==> parent in S && (parent.left == this || parent.right == this)
    requires left != null ==> left in S && left.parent == this && left != right
    requires right != null ==> right in S && right.parent == this && left != right
    requires sum + delta == val + (if left == null then 0 else left.sum) + if right == null then 0 else right.sum
    modifies U`sum
    ensures forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S ==> c.Valid(S)
    decreases delta, U, S
  {
    var p: Composite? := this;
    ghost var T := U;
    while p != null
      invariant T <= U
      invariant p == null || p.Acyclic(T)
      invariant forall c: Composite {:trigger c.Valid(S)} {:trigger c in S} :: c in S && c != p ==> c.Valid(S)
      invariant p != null ==> p.sum + delta == p.val + (if p.left == null then 0 else p.left.sum) + if p.right == null then 0 else p.right.sum
      invariant forall c: Composite {:trigger old(c.val)} {:trigger c.val} {:trigger old(c.parent)} {:trigger c.parent} {:trigger old(c.right)} {:trigger c.right} {:trigger old(c.left)} {:trigger c.left} {:trigger c in S} :: (c in S ==> c.left == old(c.left)) && (c in S ==> c.right == old(c.right)) && (c in S ==> c.parent == old(c.parent)) && (c in S ==> c.val == old(c.val))
      decreases T
    {
      p.sum := p.sum + delta;
      T := T - {p};
      p := p.parent;
    }
  }
}
