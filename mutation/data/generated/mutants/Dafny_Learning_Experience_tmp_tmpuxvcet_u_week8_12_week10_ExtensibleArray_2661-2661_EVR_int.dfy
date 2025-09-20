// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_ExtensibleArray.dfy

class ExtensibleArray<T(0)> {
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int
  var M: int

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this}
  {
    this in Repr &&
    (front != null ==>
      front in Repr) &&
    (depot != null ==>
      depot in Repr &&
      depot.Repr <= Repr &&
      forall j: int {:trigger depot.Elements[j]} :: 
        0 <= j < |depot.Elements| ==>
          depot.Elements[j] in Repr) &&
    (depot != null ==>
      this !in depot.Repr &&
      front !in depot.Repr &&
      forall j: int {:trigger depot.Elements[j]} :: 
        (0 <= j < |depot.Elements| ==>
          depot.Elements[j] !in depot.Repr) &&
        (0 <= j < |depot.Elements| ==>
          depot.Elements[j] != front) &&
        (0 <= j < |depot.Elements| ==>
          forall k: int {:trigger depot.Elements[k]} :: 
            0 <= k < |depot.Elements| &&
            k != j ==>
              depot.Elements[j] != depot.Elements[k])) &&
    (front != null ==>
      front.Length == 256) &&
    (depot != null ==>
      depot.Valid() &&
      forall j: int {:trigger depot.Elements[j]} :: 
        0 <= j < |depot.Elements| ==>
          depot.Elements[j].Length == 256) &&
    (length == M <==> front == null) &&
    M == (if depot == null then 0 else 256 * |depot.Elements|) &&
    length == |Elements| &&
    M <= |Elements| < M + 256 &&
    (forall i: int {:trigger depot.Elements[i / 256]} {:trigger Elements[i]} :: 
      0 <= i < M ==>
        Elements[i] == depot.Elements[i / 256][i % 256]) &&
    forall i: int {:trigger Elements[i]} :: 
      M <= i < length ==>
        Elements[i] == front[i - M]
  }

  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {
    front, depot := null, null;
    length, M := 0, 0;
    Elements, Repr := [], {this};
  }

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    reads Repr
    ensures Get(i) == Elements[i]
    decreases Repr, i
  {
    if M <= i then
      front[i - M]
    else
      depot.Get(i / 256)[i % 256]
  }

  method Set(i: int, t: T)
    requires Valid() && 0 <= i < |Elements|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements)[i := t]
    decreases i
  {
    if M <= i {
      front[i - M] := t;
    } else {
      depot.Get(i / 256)[i % 256] := t;
    }
    Elements := Elements[i := t];
  }

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
    decreases |Elements|
  {
    if front == null {
      front := new T[256];
      Repr := Repr + {front};
    }
    front[length - M] := t;
    length := length + 1;
    Elements := Elements + [t];
    if length == 0 + 256 {
      if depot == null {
        depot := new ExtensibleArray<array<T>>();
      }
      depot.Add(front);
      Repr := Repr + depot.Repr;
      M := M + 256;
      front := null;
    }
  }
}
