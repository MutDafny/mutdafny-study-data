// specTesting_tmp_tmpueam35lx_examples_binary_search_binary_search_specs.dfy

lemma BinarySearch(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat {:trigger intSeq[i]} | i < |intSeq| :: intSeq[i] != key
  decreases intSeq, key
{
  ghost var lo: nat := 0;
  ghost var hi: nat := |intSeq|;
  while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i: nat {:trigger intSeq[i]} | 0 <= i < lo :: intSeq[i] < key
    invariant forall i: nat {:trigger intSeq[i]} | hi <= i < |intSeq| :: intSeq[i] > key
    decreases hi - lo
  {
    ghost var mid := (lo + hi) / 2;
    if intSeq[mid] < key {
      lo := mid + 1;
    } else if intSeq[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

predicate BinarySearchTransition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat {:trigger intSeq[i]} | i < |intSeq| :: 
      intSeq[i] != key)
}

lemma BinarySearchDeterministic(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat {:trigger intSeq[i]} | i < |intSeq| :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat {:trigger intSeq[i]} | i < r :: intSeq[i] < key
  decreases intSeq, key
{
  ghost var lo: nat := 0;
  ghost var hi: nat := |intSeq|;
  while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i: nat {:trigger intSeq[i]} | 0 <= i < lo :: intSeq[i] < key
    invariant (forall i: nat {:trigger intSeq[i]} | hi <= i < |intSeq| :: intSeq[i] > key) || forall i: nat {:trigger intSeq[i]} | hi <= i < |intSeq| :: intSeq[i] >= key && exists i: nat {:trigger intSeq[i]} | lo <= i < hi :: intSeq[i] == key
    decreases hi - lo
  {
    ghost var mid := (lo + hi) / 2;
    if intSeq[mid] < key {
      lo := mid + 1;
    } else if intSeq[mid] > key {
      hi := mid;
    } else {
      assert intSeq[mid] == key;
      ghost var inner_mid := (lo + mid) / 2;
      if intSeq[inner_mid] < key {
        lo := inner_mid + 1;
      } else if hi != inner_mid + 1 {
        hi := inner_mid + 1;
      } else {
        if intSeq[lo] == key {
          return lo;
        } else {
          lo := lo + 1;
        }
      }
    }
  }
  return -1;
}

predicate BinarySearchDeterministicTransition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat {:trigger intSeq[i]} | i < |intSeq| :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat | i < r :: 
      false)
}

lemma BinarySearchWrong1(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat {:trigger intSeq[i]} | 0 < i < |intSeq| :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat {:trigger intSeq[i]} | i < r :: intSeq[i] < key
  decreases intSeq, key

predicate BinarySearchWrong1Transition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat {:trigger intSeq[i]} | 0 < i < |intSeq| :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat {:trigger intSeq[i]} | i < r :: 
      intSeq[i] < key)
}

lemma BinarySearchWrong2(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat {:trigger intSeq[i]} | 0 <= i < |intSeq| - 1 :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat {:trigger intSeq[i]} | i < r :: intSeq[i] < key
  decreases intSeq, key

predicate BinarySearchWrong2Transition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat {:trigger intSeq[i]} | 0 <= i < |intSeq| - 1 :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat {:trigger intSeq[i]} | i < r :: 
      intSeq[i] < key)
}

lemma BinarySearchWrong3(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r < 0 || (r < |intSeq| && intSeq[r] == key)
  decreases intSeq, key
{
  return -1;
}

predicate BinarySearchWrong3Transition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  r < 0 || (r < |intSeq| && intSeq[r] == key)
}

lemma BinarySearchWrong4(intSeq: seq<int>, key: int) returns (r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures 0 <= r < |intSeq| && intSeq[r] == key
  decreases intSeq, key

predicate BinarySearchWrong4Transition(intSeq: seq<int>, key: int, r: int)
  requires forall i: int, j: int {:trigger intSeq[j], intSeq[i]} | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  decreases intSeq, key, r
{
  0 <= r < |intSeq| &&
  intSeq[r] == key
}
