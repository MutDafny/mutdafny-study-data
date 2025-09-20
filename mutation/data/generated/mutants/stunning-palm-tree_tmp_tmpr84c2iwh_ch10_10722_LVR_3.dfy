// stunning-palm-tree_tmp_tmpr84c2iwh_ch10.dfy


module PQueue {
  function Empty(): PQueue
  {
    Leaf
  }

  predicate IsEmpty(pq: PQueue)
    decreases pq
  {
    pq == Leaf
  }

  function Insert(pq: PQueue, y: int): PQueue
    decreases pq, y
  {
    match pq
    case Leaf() =>
      Node(y, Leaf, Leaf)
    case Node(x, left, right) =>
      if y < x then
        Node(y, Insert(right, x), left)
      else
        Node(x, Insert(right, y), left)
  }

  function RemoveMin(pq: PQueue): (int, PQueue)
    requires Valid(pq) && !IsEmpty(pq)
    decreases pq
  {
    var Node(x: int, left: BraunTree, right: BraunTree) := pq;
    (x, DeleteMin(pq))
  }

  function DeleteMin(pq: PQueue): PQueue
    requires IsBalanced(pq) && !IsEmpty(pq)
    decreases pq
  {
    if pq.right.Leaf? then
      pq.left
    else if pq.left.x <= pq.right.x then
      Node(pq.left.x, pq.right, DeleteMin(pq.left))
    else
      Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
  }

  function ReplaceRoot(pq: PQueue, r: int): PQueue
    requires !IsEmpty(pq)
    decreases pq, r
  {
    if pq.left.Leaf? || (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x)) then
      Node(r, pq.left, pq.right)
    else if pq.right.Leaf? then
      Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
    else if pq.left.x < pq.right.x then
      Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
    else
      Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
  }

  ghost function Elements(pq: PQueue): multiset<int>
    decreases pq
  {
    match pq
    case Leaf() =>
      multiset{}
    case Node(x, left, right) =>
      multiset{x} + Elements(left) + Elements(right)
  }

  ghost predicate Valid(pq: PQueue)
    decreases pq
  {
    IsBinaryHeap(pq) &&
    IsBalanced(pq)
  }

  ghost predicate IsBinaryHeap(pq: PQueue)
    decreases pq
  {
    match pq
    case Leaf() =>
      true
    case Node(x, left, right) =>
      IsBinaryHeap(left) &&
      IsBinaryHeap(right) &&
      (left.Leaf? || x <= left.x) &&
      (right.Leaf? || x <= right.x)
  }

  ghost predicate IsBalanced(pq: PQueue)
    decreases pq
  {
    match pq
    case Leaf() =>
      true
    case Node(_ /* _v0 */, left, right) =>
      IsBalanced(left) &&
      IsBalanced(right) &&
      ghost var L: int, R: int := |Elements(left)|, |Elements(right)|; L == R || L == R + 1
  }

  lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
    requires IsBinaryHeap(pq) && y in Elements(pq)
    ensures pq.x <= y
    decreases pq, y
  {
    if pq.Node? {
      assert y in Elements(pq) ==> y == pq.x || y in Elements(pq.left) || y in Elements(pq.right);
      if y == pq.x {
        assert pq.x <= y;
      } else if y in Elements(pq.left) {
        assert pq.x <= pq.left.x;
        BinaryHeapStoresMin(pq.left, y);
        assert pq.x <= y;
      } else if y in Elements(pq.right) {
        assert pq.x <= pq.right.x;
        BinaryHeapStoresMin(pq.right, y);
        assert pq.x <= y;
      }
    }
  }

  lemma EmptyCorrect()
    ensures Valid(Empty()) && Elements(Empty()) == multiset{}
  {
  }

  lemma /*{:_inductionTrigger Elements(pq)}*/ /*{:_inductionTrigger IsEmpty(pq)}*/ /*{:_inductionTrigger Valid(pq)}*/ /*{:_induction pq}*/ IsEmptyCorrect(pq: PQueue)
    requires Valid(pq)
    ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    decreases pq
  {
    if Elements(pq) == multiset{} {
      assert pq.Leaf?;
    }
  }

  lemma /*{:_inductionTrigger Elements(pq) + multiset{y}}*/ /*{:_inductionTrigger Insert(pq, y)}*/ /*{:_induction pq, y}*/ InsertCorrect(pq: PQueue, y: int)
    requires Valid(pq)
    ensures ghost var pq': PQueue := Insert(pq, y); Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    decreases pq, y
  {
  }

  lemma /*{:_inductionTrigger Elements(pq)}*/ /*{:_inductionTrigger RemoveMin(pq)}*/ /*{:_inductionTrigger IsEmpty(pq)}*/ /*{:_inductionTrigger Valid(pq)}*/ /*{:_induction pq}*/ RemoveMinCorrect(pq: PQueue)
    requires Valid(pq)
    requires !IsEmpty(pq)
    ensures var (y: int, pq': PQueue) := RemoveMin(pq); Elements(pq) == Elements(pq') + multiset{y} && IsMin(y, Elements(pq)) && Valid(pq')
    decreases pq
  {
    DeleteMinCorrect(pq);
  }

  lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} DeleteMinCorrect(pq: PQueue)
    requires Valid(pq) && !IsEmpty(pq)
    ensures ghost var pq': PQueue := DeleteMin(pq); Valid(pq') && Elements(pq') + multiset{pq.x} == Elements(pq) && |Elements(pq')| == |Elements(pq)| - 1
    decreases pq
  {
    if pq.left.Leaf? || pq.right.Leaf? {
    } else if pq.left.x <= pq.right.x {
      DeleteMinCorrect(pq.left);
    } else {
      ghost var left, right := ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left);
      ghost var pq' := Node(pq.right.x, left, right);
      assert pq' == DeleteMin(pq);
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(left) + Elements(right) + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(left) + Elements(right) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.right, pq.left.x);
          assert multiset{pq.right.x} + Elements(left) == Elements(pq.right) + multiset{pq.left.x};
        }
        Elements(pq.right) + multiset{pq.left.x} + Elements(right) + multiset{pq.x};
      ==
        Elements(pq.right) + multiset{pq.left.x} + Elements(DeleteMin(pq.left)) + multiset{pq.x};
      ==
        Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left))) + multiset{pq.x};
      ==
        {
          DeleteMinCorrect(pq.left);
          assert multiset{pq.left.x} + Elements(DeleteMin(pq.left)) == Elements(pq.left);
        }
        Elements(pq.right) + Elements(pq.left) + multiset{pq.x};
      ==
        multiset{pq.x} + Elements(pq.right) + Elements(pq.left);
      ==
        Elements(pq);
      }
      DeleteMinCorrect(pq.left);
      assert Valid(right);
      ReplaceRootCorrect(pq.right, pq.left.x);
      assert Valid(left);
      assert pq.left.x in Elements(left);
      assert pq.right.x <= pq.left.x;
      BinaryHeapStoresMin(pq.left, pq.left.x);
      BinaryHeapStoresMin(pq.right, pq.right.x);
      assert pq.right.x <= left.x;
      assert right.Leaf? || pq.right.x <= right.x;
      assert IsBinaryHeap(pq');
    }
  }

  lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} ReplaceRootCorrect(pq: PQueue, r: int)
    requires Valid(pq) && !IsEmpty(pq)
    ensures ghost var pq': PQueue := ReplaceRoot(pq, r); Valid(pq') && r in Elements(pq') && |Elements(pq')| == |Elements(pq)| && Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x}
    decreases pq, r
  {
    ghost var pq' := ReplaceRoot(pq, r);
    ghost var left, right := pq'.left, pq'.right;
    if pq.left.Leaf? || (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x)) {
      assert Valid(pq');
      assert |Elements(pq')| == |Elements(pq)|;
    } else if pq.right.Leaf? {
    } else if pq.left.x < pq.right.x {
      assert pq.left.Node? && pq.right.Node?;
      assert pq.left.x < r || pq.right.x < r;
      assert pq' == Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right);
      ReplaceRootCorrect(pq.left, r);
      assert Valid(pq');
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.left.x} + Elements(ReplaceRoot(pq.left, r)) + Elements(pq.right) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.left, r);
        }
        Elements(pq.left) + multiset{r} + Elements(pq.right) + multiset{pq.x};
      ==
        Elements(pq) + multiset{r};
      }
    } else {
      assert pq' == Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r));
      ReplaceRootCorrect(pq.right, r);
      assert Valid(pq');
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(pq.left) + Elements(ReplaceRoot(pq.right, r)) + multiset{pq.x};
      ==
        Elements(pq.left) + (Elements(ReplaceRoot(pq.right, r)) + multiset{pq.right.x}) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.right, r);
        }
        Elements(pq.left) + multiset{r} + Elements(pq.right) + multiset{pq.x};
      ==
        Elements(pq) + multiset{r};
      }
    }
  }

  ghost predicate IsMin(y: int, s: multiset<int>)
    decreases y, s
  {
    y in s &&
    forall x: int {:trigger s[x]} :: 
      x in s ==>
        y <= x
  }

  export
    provides PQueue, Empty, IsEmpty, Insert, RemoveMin, Valid, Elements, EmptyCorrect, IsEmptyCorrect, InsertCorrect, RemoveMinCorrect
    reveals IsMin


  type /*{:_provided}*/ PQueue = BraunTree

  datatype BraunTree = Leaf | Node(x: int, left: BraunTree, right: BraunTree)
}

module PQueueClient {
  method Client()
  {
    var pq := PQ.Empty();
    PQ.EmptyCorrect();
    assert PQ.Elements(pq) == multiset{};
    assert PQ.Valid(pq);
    PQ.InsertCorrect(pq, 1);
    var pq1 := PQ.Insert(pq, 1);
    assert 1 in PQ.Elements(pq1);
    PQ.InsertCorrect(pq1, 3);
    var pq2 := PQ.Insert(pq1, 2);
    assert 2 in PQ.Elements(pq2);
    PQ.IsEmptyCorrect(pq2);
    PQ.RemoveMinCorrect(pq2);
    var (m, pq3) := PQ.RemoveMin(pq2);
    PQ.IsEmptyCorrect(pq3);
    PQ.RemoveMinCorrect(pq3);
    var (n, pq4) := PQ.RemoveMin(pq3);
    PQ.IsEmptyCorrect(pq4);
    assert PQ.IsEmpty(pq4);
    assert m <= n;
  }

  import PQ = PQueue
}
