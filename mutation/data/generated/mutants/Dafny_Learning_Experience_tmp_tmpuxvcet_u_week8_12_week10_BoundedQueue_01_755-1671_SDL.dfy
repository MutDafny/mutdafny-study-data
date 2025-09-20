// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_BoundedQueue_01.dfy

class BoundedQueue<T(0)> {
  ghost var contents: seq<T>
  ghost var N: nat
  ghost var Repr: set<object>
  var data: array<T>
  var wr: nat
  var rd: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |contents| <= N
    decreases Repr + {this}
  {
    this in Repr &&
    data in Repr &&
    data.Length == N + 1 &&
    wr <= N &&
    rd <= N &&
    contents == if rd <= wr then data[rd .. wr] else data[rd..] + data[..wr]
  }

  constructor (N: nat)
    ensures Valid() && fresh(Repr)
    ensures contents == [] && this.N == N
    decreases N
  {
    contents := [];
    this.N := N;
    data := new T[N + 1];
    rd, wr := 0, 0;
    Repr := {this, data};
  }

  method Insert(x: T)
    requires Valid()
    requires |contents| != N
    modifies Repr
    ensures contents == old(contents) + [x]
    ensures N == old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
  }

  method Remove() returns (x: T)
    requires Valid()
    requires |contents| != 0
    modifies Repr
    ensures contents == old(contents[1..]) && old(contents[0]) == x
    ensures N == old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    contents := contents[1..];
    x := data[rd];
    if rd == data.Length - 1 {
      rd := 0;
    } else {
      rd := rd + 1;
    }
  }
}
