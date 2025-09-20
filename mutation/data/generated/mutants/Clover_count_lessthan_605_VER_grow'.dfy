// Clover_count_lessthan.dfy

method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i: int {:trigger i in numbers} | i in numbers && i < threshold|
  decreases numbers, threshold
{
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink| > 0
    invariant shrink + grow == numbers
    invariant grow !! shrink
    invariant count == |set i: int {:trigger i in grow} | i in grow && i < threshold|
    decreases shrink
  {
    var i: int :| i in shrink;
    shrink := shrink - {i};
    var grow' := grow + {i};
    assert (set i: int {:trigger i in grow'} | i in grow' && i < threshold) == (set i: int {:trigger i in grow} | i in grow && i < threshold) + if i < threshold then {i} else {};
    grow := grow' + {i};
    if i < threshold {
      count := count + 1;
    }
  }
}
