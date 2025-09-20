// dafny-exercises_tmp_tmp5mvrowrx_paper_krml190.dfy

class Data { }

class Node {
  var list: seq<Data>
  var footprint: set<Node>
  var data: Data
  var next: Node?

  function Valid(): bool
    reads this, footprint
    decreases footprint + {this}
  {
    this in footprint &&
    (next == null ==>
      list == [data]) &&
    (next != null ==>
      next in footprint &&
      next.footprint <= footprint &&
      !(this in next.footprint) &&
      list == [data] + next.list &&
      next.Valid())
  }

  constructor (d: Data)
    ensures Valid() && fresh(footprint - {this})
    ensures list == [d]
    decreases d
  {
    data := d;
    next := null;
    list := [d];
    footprint := {this};
  }

  method SkipHead() returns (r: Node?)
    requires Valid()
    ensures r == null ==> |list| == 1
    ensures r != null ==> r.Valid() && r.footprint <= footprint
  {
    return next;
  }

  method Prepend(d: Data) returns (r: Node)
    requires Valid()
    ensures r.Valid() && fresh(r.footprint - old(footprint))
    ensures r.list == [d] + list
    decreases d
  {
    r := new Node(d);
    r.data := d;
    r.next := this;
    r.footprint := {r} + footprint;
    r.list := [r.data] + list;
  }

  method ReverseInPlace() returns (reverse: Node)
    requires Valid()
    modifies footprint
    ensures reverse.Valid()
    ensures fresh(reverse.footprint - old(footprint))
    ensures |reverse.list| == |old(list)|
    ensures forall i: int {:trigger old(list)[i]} | 0 <= i < |old(list)| :: old(list)[i] == reverse.list[|old(list)| - 1 - i]
  {
    var current: Node?;
    current := next;
    reverse := this;
    reverse.next := null;
    reverse.footprint := {reverse};
    reverse.list := [data];
    while current != null
      invariant reverse.Valid()
      invariant reverse.footprint <= old(footprint)
      invariant current == null ==> |old(list)| == |reverse.list|
      invariant current != null ==> current.Valid()
      invariant current != null ==> current in old(footprint) && current.footprint <= old(footprint)
      invariant current != null ==> current.footprint !! reverse.footprint
      invariant current != null ==> |old(list)| == |reverse.list| + |current.list|
      invariant current != null ==> forall i: int {:trigger current.list[i]} | 0 <= i < |current.list| :: current.list[i] == old(list)[|reverse.list| + i]
      invariant forall i: int {:trigger old(list)[i]} | 0 <= i < |reverse.list| :: old(list)[i] == reverse.list[|reverse.list| - 1 - i]
      decreases |old(list)| - |reverse.list|
    {
      var nx: Node?;
      nx := current.next;
      assert nx != null ==> forall i: int {:trigger nx.list[i]} | 0 <= i < |nx.list| :: current.list[i + 1] == nx.list[i];
      assert current.data == current.list[0];
      current.next := reverse;
      current.footprint := {current} + reverse.footprint;
      current.list := [current.data] + reverse.list;
      reverse := current;
    }
  }
}
