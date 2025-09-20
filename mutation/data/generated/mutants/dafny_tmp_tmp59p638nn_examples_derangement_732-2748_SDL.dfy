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
}
