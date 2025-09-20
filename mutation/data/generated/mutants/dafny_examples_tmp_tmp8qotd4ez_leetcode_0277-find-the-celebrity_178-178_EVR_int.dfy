// dafny_examples_tmp_tmp8qotd4ez_leetcode_0277-find-the-celebrity.dfy

predicate knows(a: int, b: int)
  decreases a, b

predicate isCelebrity(n: int, i: int)
  requires n >= 0 && 0 <= i < n
  decreases n, i
{
  forall j: int {:trigger knows(i, j)} {:trigger knows(j, 0)} :: 
    (0 <= j < n &&
    i != j ==>
      knows(j, 0)) &&
    (0 <= j < n &&
    i != j ==>
      !knows(i, j))
}

lemma knowerCannotBeCelebrity(n: int, i: int)
  requires n >= 0 && 0 <= i < n
  ensures (exists j: int {:trigger knows(i, j)} :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
  decreases n, i
{
}

ghost method isCelebrityP(n: int, i: int) returns (r: bool)
  requires n >= 0 && 0 <= i < n
  ensures r <==> isCelebrity(n, i)
  decreases n, i
{
  ghost var j := 0;
  r := true;
  while j < n
    invariant 0 <= j <= n
    invariant r ==> forall k: int {:trigger knows(i, k)} {:trigger knows(k, i)} :: (0 <= k < j && k != i ==> knows(k, i)) && (0 <= k < j && k != i ==> !knows(i, k))
    decreases n - j
  {
    if j != i {
      if !knows(j, i) || knows(i, j) {
        return false;
      }
    }
    j := j + 1;
  }
  return r;
}

ghost method findCelebrity(n: int) returns (r: int)
  requires 2 <= n <= 100
  ensures 0 <= r < n ==> isCelebrity(n, r)
  ensures r == -1 ==> forall i: int {:trigger isCelebrity(n, i)} :: 0 <= i < n ==> !isCelebrity(n, i)
  decreases n
{
  ghost var candidate := 0;
  ghost var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j: int {:trigger isCelebrity(n, j)} :: 0 <= j < i && j != candidate ==> !isCelebrity(n, j)
    invariant 0 <= candidate < i
    decreases n - i
  {
    if knows(candidate, i) {
      candidate := i;
    }
    i := i + 1;
  }
  ghost var isCelebrityC := isCelebrityP(n, candidate);
  if isCelebrityC {
    r := candidate;
  } else {
    r := -1;
  }
}
