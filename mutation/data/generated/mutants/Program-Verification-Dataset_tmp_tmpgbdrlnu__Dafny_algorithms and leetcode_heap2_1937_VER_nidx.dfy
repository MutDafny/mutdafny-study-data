// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_heap2.dfy

class Heap {
  var arr: array<int>

  constructor Heap(input: array<int>)
    ensures this.arr == input
    decreases input
  {
    this.arr := input;
  }

  function parent(idx: int): int
    decreases idx
  {
    if idx == 0 then
      -1
    else if idx % 2 == 0 then
      (idx - 2) / 2
    else
      (idx - 1) / 2
  }

  predicate IsMaxHeap(input: seq<int>)
    decreases input
  {
    (forall i: int, _t#0: int {:trigger input[_t#0], input[i]} {:trigger input[_t#0], 2 * i} | _t#0 == 2 * i + 1 :: 
      0 <= i &&
      i < |input| ==>
        _t#0 < |input| ==>
          input[i] >= input[_t#0]) &&
    forall i: int, _t#0: int {:trigger input[_t#0], input[i]} {:trigger input[_t#0], 2 * i} | _t#0 == 2 * i + 2 :: 
      0 <= i &&
      i < |input| ==>
        _t#0 < |input| ==>
          input[i] >= input[_t#0]
  }

  predicate IsAlmostMaxHeap(input: seq<int>, idx: int)
    requires 0 <= idx
    decreases input, idx
  {
    (forall i: int, _t#0: int {:trigger input[_t#0], input[i]} {:trigger input[_t#0], 2 * i} | _t#0 == 2 * i + 1 :: 
      0 <= i &&
      i < |input| ==>
        _t#0 < |input| &&
        i != idx ==>
          input[i] >= input[_t#0]) &&
    (forall i: int, _t#0: int {:trigger input[_t#0], input[i]} {:trigger input[_t#0], 2 * i} | _t#0 == 2 * i + 2 :: 
      0 <= i &&
      i < |input| ==>
        _t#0 < |input| &&
        i != idx ==>
          input[i] >= input[_t#0]) &&
    (0 <= parent(idx) < |input| &&
    2 * idx + 1 < |input| ==>
      input[parent(idx)] >= input[2 * idx + 1]) &&
    (0 <= parent(idx) < |input| &&
    2 * idx + 2 < |input| ==>
      input[parent(idx)] >= input[2 * idx + 2])
  }

  method heapify(idx: int) returns (nidx: int)
    requires 0 <= idx < this.arr.Length
    requires IsAlmostMaxHeap(this.arr[..], idx)
    modifies this, this.arr
    ensures nidx == -1 || idx < nidx < this.arr.Length
    ensures nidx == -1 ==> IsMaxHeap(this.arr[..])
    ensures idx < nidx < this.arr.Length ==> IsAlmostMaxHeap(this.arr[..], nidx)
    decreases idx
  {
    if 2 * idx + 1 >= this.arr.Length && 2 * idx + 2 >= this.arr.Length {
      nidx := -1;
      assert IsMaxHeap(this.arr[..]);
      return;
    } else {
      assert 2 * idx + 1 < this.arr.Length || 2 * idx + 2 < this.arr.Length;
      nidx := idx;
      if 2 * idx + 1 < this.arr.Length && this.arr[nidx] < this.arr[2 * idx + 1] {
        nidx := 2 * idx + 1;
      }
      if 2 * idx + 2 < this.arr.Length && this.arr[nidx] < this.arr[2 * idx + 2] {
        nidx := 2 * idx + 2;
      }
      if nidx == idx {
        nidx := -1;
        return;
      } else {
        assert nidx == 2 * idx + 1 || nidx == 2 * idx + 2;
        this.arr[idx], this.arr[nidx] := this.arr[nidx], this.arr[nidx];
        forall i: int | 0 <= i < this.arr.Length
          ensures i != nidx && 2 * i + 1 < this.arr.Length ==> this.arr[i] >= this.arr[2 * i + 1]
        {
          if i != nidx && 2 * i + 1 < this.arr.Length {
            if 2 * i + 1 == idx {
              assert this.arr[i] >= this.arr[2 * i + 1];
            }
          }
        }
        forall i: int | 0 <= i < this.arr.Length
          ensures i != nidx && 2 * i + 2 < this.arr.Length ==> this.arr[i] >= this.arr[2 * i + 2]
        {
          if i != nidx && 2 * i + 2 < this.arr.Length {
            if 2 * i + 2 == idx {
              assert this.arr[i] >= this.arr[2 * i + 2];
            }
          }
        }
      }
    }
  }
}
