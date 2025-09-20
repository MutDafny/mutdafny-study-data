// Dafny-Practice_tmp_tmphnmt4ovh_BST.dfy

method Main()
{
  var tree := BuildBST([-2, 8, 3, 9, 2, -7, 0]);
  PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree)
  decreases t
{
  match t {
    case {:split false} Empty() =>
    case {:split false} Node(n, l, r) =>
      PrintTreeNumbersInorder(l);
      print n;
      print "\n";
      PrintTreeNumbersInorder(r);
  }
}

function NumbersInTree(t: Tree): set<int>
  decreases t
{
  NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
  decreases q
{
  set x: int {:trigger x in q} | x in q
}

predicate BST(t: Tree)
  decreases t
{
  Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
  decreases t
{
  match t {
    case Empty() =>
      []
    case Node(n', nt1, nt2) =>
      Inorder(nt1) + [n'] + Inorder(nt2)
  }
}

predicate Ascending(q: seq<int>)
  decreases q
{
  forall i: int, j: int {:trigger q[j], q[i]} :: 
    0 <= i < j < |q| ==>
      q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>)
  decreases q
{
  forall i: int, j: int {:trigger q[j], q[i]} :: 
    0 <= i < j < |q| ==>
      q[i] != q[j]
}

method BuildBST(q: seq<int>) returns (t: Tree)
  requires NoDuplicates(q)
  ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
  decreases q
{
  t := Empty;
  for i: int := 0 to |q|
    invariant BST(t)
    invariant NumbersInTree(t) == NumbersInSequence(q[..i])
  {
    t := InsertBST(t, q[i]);
  }
}

method InsertBST(t0: Tree, x: int) returns (t: Tree)
  requires BST(t0) && x !in NumbersInTree(t0)
  ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
  decreases t0, x
{
  match t0 {
    case {:split false} Empty() =>
      t := Node(x, Empty, Empty);
  }
}

lemma LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
  requires BST(Node(n, left, right))
  ensures BST(left) && BST(right)
  decreases n, left, right
{
  assert Ascending(Inorder(Node(n, left, right)));
  ghost var qleft, qright := Inorder(left), Inorder(right);
  ghost var q := qleft + [n] + qright;
  assert q == Inorder(Node(n, left, right));
  assert Ascending(qleft + [n] + qright);
  assert Ascending(qleft) by {
    LemmaAscendingSubsequence(q, qleft, 0);
  }
  assert Ascending(qright) by {
    LemmaAscendingSubsequence(q, qright, |qleft| + 1);
  }
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
  requires i <= |q1| - |q2| && q2 == q1[i .. i + |q2|]
  requires Ascending(q1)
  ensures Ascending(q2)
  decreases q1, q2, i
{
}

lemma {:verify true} lemma_all_small(q: seq<int>, i: int)
  requires forall k: int {:trigger k in NumbersInSequence(q)} :: k in NumbersInSequence(q) ==> k < i
  requires forall k: int {:trigger q[k]} :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
  ensures forall j: int {:trigger q[j]} :: 0 <= j < |q| ==> q[j] < i
  decreases q, i
{
}

lemma {:verify true} lemma_all_big(q: seq<int>, i: int)
  requires forall k: int {:trigger k in NumbersInSequence(q)} :: k in NumbersInSequence(q) ==> k > i
  requires forall k: int {:trigger q[k]} :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
  ensures forall j: int {:trigger q[j]} :: 0 <= j < |q| ==> q[j] > i
  decreases q, i
{
}

datatype Tree = Empty | Node(int, Tree, Tree)
