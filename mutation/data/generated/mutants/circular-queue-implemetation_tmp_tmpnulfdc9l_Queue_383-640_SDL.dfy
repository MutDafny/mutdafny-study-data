// circular-queue-implemetation_tmp_tmpnulfdc9l_Queue.dfy

method Main()
{
  var circularQueue := new Queue();
  assert circularQueue.circularQueue.Length == 0;
  assert circularQueue.Content == [];
  assert circularQueue.Content != [1];
  var isQueueEmpty := circularQueue.isEmpty();
  assert isQueueEmpty == true;
  var queueSize := circularQueue.size();
  assert queueSize == 0;
  circularQueue.auxInsertEmptyQueue(2);
  assert circularQueue.Content == [2];
  assert circularQueue.counter == 1;
  assert circularQueue.circularQueue.Length == 1;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 1;
  assert circularQueue.rear != 2;
  assert circularQueue.front != 2;
  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2, 4];
  assert circularQueue.counter == 2;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 2;
  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2, 4, 4];
  assert circularQueue.counter == 3;
  circularQueue.auxInsertEndQueue(56);
  assert circularQueue.Content == [2, 4, 4, 56];
  assert circularQueue.counter == 4;
  var contains56 := circularQueue.contains(56);
  assert contains56 == true;
  var contains4 := circularQueue.contains(4);
  assert contains4 == true;
  var item := circularQueue.remove();
  assert item == 2;
  assert (0 + 1) % 6 == 1;
  assert (1 + 1) % 6 == 2;
  assert (2 + 1) % 6 == 3;
  assert (3 + 1) % 6 == 4;
  assert (4 + 1) % 6 == 5;
  assert (5 + 1) % 6 == 0;
  assert (0 + 1) % 6 == 1;
}

class {:autocontracts} Queue {
  var circularQueue: array<int>
  var rear: nat
  var front: nat
  var counter: nat
  ghost var Content: seq<int>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this}
  {
    this in Repr &&
    null !in Repr &&
    circularQueue in Repr &&
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  constructor ()
    ensures Valid()
    ensures fresh(Repr)
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == []
    ensures counter == 0
  {
    new;
    Repr := {this};
    if !(circularQueue in Repr) {
      Repr := Repr + {circularQueue};
    }
  }

  method insert(item: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    decreases item
  {
    if !(circularQueue in Repr) {
      Repr := Repr + {circularQueue};
    }
  }

  method auxInsertEmptyQueue(item: int)
    requires Valid()
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
    decreases item
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int[circularQueue.Length + 1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := rear + 1;
    if !(circularQueue in Repr) {
      Repr := Repr + {circularQueue};
    }
  }

  method auxInsertEndQueue(item: int)
    requires Valid()
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    decreases item

  method auxInsertSpaceQueue(item: int)
    requires Valid()
    requires rear < front && front < circularQueue.Length
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0 .. rear]) + [item] + old(Content[rear + 1 .. circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
    decreases item

  method auxInsertInitQueue(item: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    decreases item

  method auxInsertBetweenQueue(item: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    decreases item

  method remove() returns (item: int)
    requires Valid()
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front) .. rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front) .. |old(Content)|]

  method size() returns (size: nat)
    requires Valid()
    ensures size == counter
  {
    size := counter;
  }

  method isEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty == true ==> counter == 0
    ensures isEmpty == false ==> counter != 0
  {
    isEmpty := if counter == 0 then true else false;
  }

  method contains(item: int) returns (contains: bool)
    requires Valid()
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
    decreases item
  {
    var i: nat := 0;
    contains := false;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant !contains ==> forall j: int {:trigger circularQueue[j]} :: 0 <= j < i ==> circularQueue[j] != item
      decreases circularQueue.Length - i
    {
      if circularQueue[i] == item {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    decreases otherQueue
  {
    var newQueueSize: int := otherQueue.circularQueue.Length + circularQueue.Length;
    var newFront: int := front;
    var newRear: int := otherQueue.rear;
    var tmp: array<int> := new int[newQueueSize];
    forall i: int | 0 <= i < circularQueue.Length {
      tmp[i] := circularQueue[i];
    }
    mergedQueue := new Queue();
    if !(circularQueue in Repr) {
      Repr := Repr + {circularQueue};
    }
  }

  ghost var Repr: set<object?>
}
