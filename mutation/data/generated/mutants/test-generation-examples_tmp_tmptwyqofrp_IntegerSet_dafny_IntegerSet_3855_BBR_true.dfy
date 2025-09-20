// test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_IntegerSet.dfy


module IntegerSet {
  class Set {
    var elements: seq<int>

    constructor Set0()
      ensures this.elements == []
      ensures |this.elements| == 0
    {
      this.elements := [];
    }

    constructor Set(elements: seq<int>)
      requires forall i: int, j: int {:trigger elements[j], elements[i]} | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      ensures this.elements == elements
      ensures forall i: int, j: int {:trigger this.elements[j], this.elements[i]} | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      decreases elements
    {
      this.elements := elements;
    }

    method size() returns (size: int)
      ensures size == |elements|
    {
      size := |elements|;
    }

    method addElement(element: int)
      requires forall i: int, j: int {:trigger elements[j], elements[i]} | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      modifies this`elements
      ensures element in old(elements) ==> elements == old(elements)
      ensures element !in old(elements) ==> |elements| == |old(elements)| + 1 && element in elements && forall i: int {:trigger i in elements} {:trigger i in old(elements)} :: i in old(elements) ==> i in elements
      ensures forall i: int, j: int {:trigger elements[j], elements[i]} | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      decreases element
    {
      if element !in elements {
        elements := elements + [element];
      }
    }

    method removeElement(element: int)
      requires forall i: int, j: int {:trigger elements[j], elements[i]} | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      modifies this`elements
      ensures element in old(elements) ==> |elements| == |old(elements)| - 1 && (forall i: int {:trigger i in elements} {:trigger i in old(elements)} :: i in old(elements) && i != element <==> i in elements) && element !in elements
      ensures element !in old(elements) ==> elements == old(elements)
      ensures forall i: int, j: int {:trigger elements[j], elements[i]} | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      decreases element
    {
      if element in elements {
        var i := 0;
        while 0 <= i < |elements|
          invariant 0 <= i < |elements|
          invariant forall j: int {:trigger elements[j]} :: 0 <= j < i < |elements| ==> elements[j] != element
          decreases |elements| - i
        {
          if elements[i] == element {
            if i < |elements| - 1 && i != -1 {
              elements := elements[..i] + elements[i + 1..];
            } else if i == |elements| - 1 {
              elements := elements[..i];
            }
            break;
          }
          i := i + 1;
        }
      }
    }

    method contains(element: int) returns (contains: bool)
      ensures contains == (element in elements)
      ensures elements == old(elements)
      decreases element
    {
      contains := false;
      if element in elements {
        contains := true;
      }
    }

    function intersect_length(s1: seq<int>, s2: seq<int>, count: int, start: int, stop: int): int
      requires 0 <= start <= stop
      requires stop <= |s1|
      decreases stop - start
    {
      if start == stop then
        count
      else
        if s1[start] in s2 then intersect_length(s1, s2, count + 1, start + 1, stop) else intersect_length(s1, s2, count, start + 1, stop)
    }

    function union_length(s1: seq<int>, s2: seq<int>, count: int, i: int, stop: int): int
      requires 0 <= i <= stop
      requires stop <= |s1|
      decreases stop - i
    {
      if true then
        count
      else
        if s1[i] !in s2 then union_length(s1, s2, count + 1, i + 1, stop) else union_length(s1, s2, count, i + 1, stop)
    }

    method intersect(s: Set) returns (intersection: Set)
      requires forall i: int, j: int {:trigger s.elements[j], s.elements[i]} | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
      requires forall i: int, j: int {:trigger this.elements[j], this.elements[i]} | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
      ensures forall i: int {:trigger i in this.elements} {:trigger i in s.elements} {:trigger i in intersection.elements} :: i in intersection.elements <==> i in s.elements && i in this.elements
      ensures forall i: int {:trigger i in this.elements} {:trigger i in s.elements} {:trigger i in intersection.elements} :: i !in intersection.elements <==> i !in s.elements || i !in this.elements
      ensures forall j: int, k: int {:trigger intersection.elements[k], intersection.elements[j]} | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k]
      ensures fresh(intersection)
      decreases s
    {
      intersection := new Set.Set0();
      var inter: seq<int> := [];
      var i := 0;
      while 0 <= i < |this.elements|
        invariant 0 <= i < |this.elements| || i == 0
        invariant forall j: int, k: int {:trigger inter[k], inter[j]} | 0 <= j < |inter| && 0 <= k < |inter| && j != k :: inter[j] != inter[k]
        invariant forall j: int {:trigger this.elements[j]} :: 0 <= j < i < |this.elements| ==> (this.elements[j] in inter <==> this.elements[j] in s.elements)
        invariant forall j: int {:trigger inter[j]} :: (0 <= j < |inter| ==> inter[j] in this.elements) && (0 <= j < |inter| ==> inter[j] in s.elements)
        invariant |inter| <= i <= |this.elements|
        decreases |this.elements| - i
      {
        var old_len := |inter|;
        if this.elements[i] in s.elements && this.elements[i] !in inter {
          inter := inter + [this.elements[i]];
        }
        if i == |this.elements| - 1 {
          assert old_len + 1 == |inter| || old_len == |inter|;
          break;
        }
        assert old_len + 1 == |inter| || old_len == |inter|;
        i := i + 1;
      }
      intersection.elements := inter;
    }

    method union(s: Set) returns (union: Set)
      requires forall i: int, j: int {:trigger s.elements[j], s.elements[i]} | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
      requires forall i: int, j: int {:trigger this.elements[j], this.elements[i]} | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
      ensures forall i: int {:trigger i in union.elements} {:trigger i in this.elements} {:trigger i in s.elements} :: i in s.elements || i in this.elements <==> i in union.elements
      ensures forall i: int {:trigger i in union.elements} {:trigger i in this.elements} {:trigger i in s.elements} :: i !in s.elements && i !in this.elements <==> i !in union.elements
      ensures forall j: int, k: int {:trigger union.elements[k], union.elements[j]} | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
      ensures fresh(union)
      decreases s
    {
      var elems := s.elements;
      union := new Set.Set0();
      var i := 0;
      while 0 <= i < |this.elements|
        invariant 0 <= i < |this.elements| || i == 0
        invariant forall j: int {:trigger s.elements[j]} :: 0 <= j < |s.elements| ==> s.elements[j] in elems
        invariant forall j: int {:trigger this.elements[j]} :: 0 <= j < i < |this.elements| ==> (this.elements[j] in elems <==> this.elements[j] in s.elements || this.elements[j] in this.elements)
        invariant forall j: int {:trigger elems[j]} :: 0 <= j < |elems| ==> elems[j] in this.elements || elems[j] in s.elements
        invariant forall j: int, k: int {:trigger elems[k], elems[j]} :: 0 <= j < |elems| && 0 <= k < |elems| && j != k ==> elems[j] != elems[k]
        decreases |this.elements| - i
      {
        if this.elements[i] !in elems {
          elems := elems + [this.elements[i]];
        }
        if i == |this.elements| - 1 {
          break;
        }
        i := i + 1;
      }
      union.elements := elems;
    }
  }
}
