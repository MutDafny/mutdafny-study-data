// dafny_tmp_tmp59p638nn_examples_derangement.dfy

predicate derangement(s: seq<nat>)
  decreases s
{
  forall i: int {:trigger s[i]} :: 
    0 <= i < |s| ==>
      s[i] != i
}

predicate permutation(s: seq<nat>)
  decreases s
{
  forall i: int {:trigger i in s} :: 
    0 <= i < |s| ==>
      i in s
}

function multisetRange(n: nat): multiset<nat>
  decreases n
{
  multiset(seq(n, (i: int) => i))
}

predicate distinct<A(==)>(s: seq<A>)
  decreases s
{
  forall x: int, y: int {:trigger s[y], s[x]} :: 
    x != y &&
    0 <= x <= y < |s| ==>
      s[x] != s[y]
}

method test()
{
  var tests := [2, 0, 1];
  var tests2 := [0, 1, 2];
  var t4 := seq(3, (i: int) => i);
  var test3 := multisetRange(3);
  assert t4 == tests2;
  assert 0 in t4;
  assert 0 in test3;
  assert multiset(tests) == multisetRange(3);
  assert derangement(tests);
  assert permutation(tests);
  assert permutation(tests2);
}

method {:timelimit 40} end(links: seq<nat>)
  requires |links| > 0
  requires permutation(links)
  requires derangement(links)
  requires distinct(links)
  decreases links
{
  assume forall x: int {:trigger x in links} :: (x in links ==> 0 <= x) && (x in links ==> x < |links|);
  assume forall x: int {:trigger multiset(links)[x]} {:trigger x in links} :: x in links ==> multiset(links)[x] == 1;
  var qAct: nat := links[0];
  assert links[0] in links;
  var i: nat := 0;
  ghost var oldIndex := 0;
  ghost var indices: multiset<nat> := multiset{0};
  ghost var visited: multiset<nat> := multiset{};
  while qAct != 0
    invariant 0 <= oldIndex < |links|
    invariant qAct == links[oldIndex]
    invariant oldIndex in indices
    invariant qAct in links
    invariant indices == visited + multiset{0}
    invariant forall x: int {:trigger visited[x]} :: x in visited ==> exists k: int {:trigger indices[k]} {:trigger links[k]} :: 0 <= k < |links| && links[k] == x && k in indices
    invariant qAct !in visited
    invariant 0 <= qAct < |links|
    decreases multiset(links) - visited
  {
    ghost var oldVisit := visited;
    ghost var oldqAct := qAct;
    ghost var oldOldIndex := oldIndex;
    oldIndex := qAct;
    visited := visited + multiset{qAct};
    indices := indices + multiset{qAct};
    assert oldqAct in visited;
    assert forall x: int {:trigger visited[x]} :: x in visited ==> exists k: int {:trigger indices[k]} {:trigger links[k]} :: 0 <= k < |links| && links[k] == x && k in indices;
    qAct := links[qAct];
    i := -(i + 1);
  }
}
