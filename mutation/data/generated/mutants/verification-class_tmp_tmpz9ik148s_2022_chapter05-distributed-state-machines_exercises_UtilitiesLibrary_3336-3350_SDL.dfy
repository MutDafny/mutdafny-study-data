// verification-class_tmp_tmpz9ik148s_2022_chapter05-distributed-state-machines_exercises_UtilitiesLibrary.dfy


module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>): seq<T>
    requires 0 < |theSeq|
    decreases theSeq
  {
    theSeq[..|theSeq| - 1]
  }

  function Last<T>(theSeq: seq<T>): T
    requires 0 < |theSeq|
    decreases theSeq
  {
    theSeq[|theSeq| - 1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>): set<T>
    decreases theSets
  {
    if |theSets| == 0 then
      {}
    else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  lemma /*{:_inductionTrigger UnionSeqOfSets(theSets)}*/ /*{:_inductionTrigger |theSets|}*/ /*{:_induction theSets}*/ SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx: int {:trigger theSets[idx]} | 0 <= idx < |theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
    decreases theSets
  {
  }

  lemma /*{:_inductionTrigger |theSets|}*/ /*{:_inductionTrigger UnionSeqOfSets(theSets)}*/ /*{:_induction theSets}*/ EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member: T {:trigger member in UnionSeqOfSets(theSets)} | member in UnionSeqOfSets(theSets) :: exists idx: int {:trigger theSets[idx]} :: 0 <= idx < |theSets| && member in theSets[idx]
    decreases theSets
  {
  }

  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx: int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0 <= idx < |theSets|
    ensures member in theSets[idx]
    decreases theSets
  {
    EachUnionMemberBelongsToASet(theSets);
    ghost var chosenIdx :| 0 <= chosenIdx < |theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  function {:opaque} MapRemoveOne<K, V>(m: map<K, V>, key: K): (m': map<K, V>)
    ensures forall k: K {:trigger k in m'} {:trigger k in m} :: k in m && k != key ==> k in m'
    ensures forall k: K {:trigger k in m} {:trigger k in m'} :: (k in m' ==> k in m) && (k in m' ==> k != key)
    ensures forall j: K {:trigger m[j]} {:trigger m'[j]} {:trigger j in m'} :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
    decreases m
  {
    var m': map<K, V> := map j: K {:trigger m[j]} {:trigger j in m} | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  function TurnRight(direction: Direction): Direction
    decreases direction
  {
    if direction.North? then
      East
    else if direction.East? then
      South
    else if direction.South? then
      West
    else
      North
  }

  lemma Rotation()
  {
    assert TurnRight(North) == East;
  }

  function TurnLeft(direction: Direction): Direction
    decreases direction
  {
    match direction {
      case North() =>
        West
      case West() =>
        South
      case East() =>
        North
    }
  }

  datatype Option<T> = Some(value: T) | None

  datatype Direction = North | East | South | West

  datatype Meat = Salami | Ham

  datatype Cheese = Provolone | Swiss | Cheddar | Jack

  datatype Veggie = Olive | Onion | Pepper

  datatype Order = Sandwich(meat: Meat, cheese: Cheese) | Pizza(meat: Meat, veggie: Veggie) | Appetizer(cheese: Cheese)
}
