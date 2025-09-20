// dafny_projects_tmp_tmpjutqwjv4_tutorial_tutorial.dfy

function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (ret: nat)
  ensures ret == fib(n)
  decreases n
{
  var a := 0;
  var b := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - i
  {
    a, b := b, a + b;
    i := i + 1;
  }
  assert i == n;
  return a;
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] != key
  decreases a, key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k: int {:trigger a[k]} :: 0 <= k < index ==> a[k] != key
    decreases a.Length - index
  {
    if a[index] == key {
      return index;
    }
    index := index + 1;
  }
  return -1;
}

predicate sorted(a: array<int>)
  reads a
  decreases {a}, a
{
  forall n: int, m: int {:trigger a[m], a[n]} :: 
    0 <= n < m < a.Length ==>
      a[n] <= a[m]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> a[k] != value
  decreases a, value
{
  var low := 0;
  var high := a.Length - 1;
  while low < high
    invariant 0 <= low && high < a.Length
    invariant forall k: int {:trigger a[k]} :: 0 <= k < a.Length && (k < low || k > high) ==> a[k] != value
    decreases high - low
  {
    var mid: int := (low + high) / 2;
    assert 0 <= low <= mid < high < a.Length;
    if a[mid] < value {
      low := mid + 1;
    } else if a[mid] > value {
      high := mid - 1;
    } else {
      assert a[mid] == value;
      return mid;
    }
  }
  if low < a.Length && a[low] == value {
    return high;
  } else {
    return -1;
  }
}

function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
  decreases s, i, v
{
  s[..i] + [v] + s[i + 1..]
}

lemma SkippingLemma(a: array<int>, j: int)
  requires forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i: int, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 0 < i && i < a.Length ==> a[_t#0] - 1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i: int {:trigger a[i]} :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
  decreases a, j
{
  ghost var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[i] >= a[j] - (i - j)
    invariant forall k: int {:trigger a[k]} :: j <= k < i && k < a.Length ==> a[k] != 0
    decreases j + a[j] - i, if i < j + a[j] then a.Length - i else 0 - 1
  {
    i := i + 1;
  }
}

method FindZero(a: array<int>) returns (index: int)
  requires forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i: int, _t#0: int {:trigger a[i], a[_t#0]} | _t#0 == i - 1 :: 0 < i && i < a.Length ==> a[_t#0] - 1 <= a[i]
  ensures index < 0 ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
  decreases a
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k: int {:trigger a[k]} :: 0 <= k < index && k < a.Length ==> a[k] != 0
    decreases a.Length - index
  {
    if a[index] == 0 {
      return;
    }
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}

function count(a: seq<bool>): nat
  decreases a
{
  if |a| == 0 then
    0
  else
    (if a[0] then 1 else 0) + count(a[1..])
}

lemma /*{:_inductionTrigger a + b}*/ /*{:_induction a, b}*/ DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
  decreases a, b
{
  if a == [] {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
  }
}

predicate closed(graph: set<Node>)
  reads graph
  decreases graph, graph
{
  forall i: Node {:trigger i.next} :: 
    i in graph ==>
      forall k: int {:trigger i.next[k]} :: 
        (0 <= k < |i.next| ==>
          i.next[k] in graph) &&
        (0 <= k < |i.next| ==>
          i.next[k] != i)
}

predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
  decreases graph, p, graph
{
  p[0] in graph &&
  (|p| > 1 ==>
    p[1] in p[0].next &&
    path(p[1..], graph))
}

predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
  decreases graph, p, start, end, graph
{
  0 < |p| &&
  start == p[0] &&
  end == p[|p| - 1] &&
  path(p, graph)
}

lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
  decreases p, subgraph, root, goal, graph
{
  if |p| >= 2 && p[0] == root && p[1] in p[0].next {
    DisproofLemma(p[1..], subgraph, p[1], goal, graph);
  }
}

lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !exists p: seq<Node> {:trigger pathSpecific(p, root, goal, graph)} :: pathSpecific(p, root, goal, graph)
  decreases subgraph, root, goal, graph
{
  forall p: seq<Node> | true {
    DisproofLemma(p, subgraph, root, goal, graph);
  }
}

class Node {
  var next: seq<Node>
}
