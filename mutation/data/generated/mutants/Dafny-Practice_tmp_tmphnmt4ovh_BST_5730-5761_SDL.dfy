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
    case {:split false} Node(i, left, right) =>
      {
        var tmp: Tree := Empty;
        if x < i {
          LemmaBinarySearchSubtree(i, left, right);
          tmp := InsertBST(left, x);
          t := Node(i, tmp, right);
          ghost var right_nums := Inorder(right);
          ghost var left_nums := Inorder(left);
          ghost var all_nums := Inorder(t0);
          assert all_nums == left_nums + [i] + right_nums;
          assert all_nums[|left_nums|] == i;
          assert all_nums[|left_nums| + 1..] == right_nums;
          assert Ascending(right_nums);
          assert Ascending(left_nums);
          assert Ascending(left_nums + [i] + right_nums);
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: (|left_nums| < j < k < |all_nums| ==> x < i) && (|left_nums| < j < k < |all_nums| ==> i < all_nums[j]) && (|left_nums| < j < k < |all_nums| ==> all_nums[j] < all_nums[k]);
          ghost var new_all_nums := Inorder(t);
          ghost var new_left_nums := Inorder(tmp);
          assert new_all_nums == new_left_nums + [i] + right_nums;
          assert Ascending([i] + right_nums);
          assert Ascending(new_left_nums);
          assert NumbersInSequence(new_left_nums) == NumbersInSequence(left_nums) + {x};
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: 0 <= j < k < |all_nums| ==> all_nums[j] < all_nums[k];
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: (0 <= j < k < |left_nums| ==> all_nums[j] < all_nums[k]) && (0 <= j < k < |left_nums| ==> all_nums[k] < all_nums[|left_nums|]);
          assert all_nums[|left_nums|] == i;
          assert left_nums == all_nums[..|left_nums|];
          assert NumbersInSequence(new_left_nums) == NumbersInSequence(all_nums[..|left_nums|]) + {x};
          assert forall j: int, k: int {:trigger left_nums[k], left_nums[j]} :: (0 <= j < k < |left_nums| ==> left_nums[j] < left_nums[k]) && (0 <= j < k < |left_nums| ==> left_nums[k] < i);
          assert x < i;
          assert forall j: int {:trigger j in NumbersInSequence(all_nums[..|left_nums|])} :: j in NumbersInSequence(all_nums[..|left_nums|]) ==> j < i;
          assert forall j: int {:trigger j in NumbersInSequence(all_nums[..|left_nums|]) + {x}} :: j in NumbersInSequence(all_nums[..|left_nums|]) + {x} ==> j < i;
          assert forall j: int {:trigger j in NumbersInSequence(new_left_nums)} :: j in NumbersInSequence(new_left_nums) ==> j < i;
          assert forall j: int {:trigger j in new_left_nums} {:trigger j in NumbersInSequence(new_left_nums)} :: j in NumbersInSequence(new_left_nums) <==> j in new_left_nums;
          assert forall j: int, k: int {:trigger new_left_nums[k], new_left_nums[j]} :: 0 <= j < k < |new_left_nums| ==> new_left_nums[j] < new_left_nums[k];
          assert x < i;
          lemma_all_small(new_left_nums, i);
          assert forall j: int {:trigger new_left_nums[j]} :: 0 <= j < |new_left_nums| ==> new_left_nums[j] < i;
          assert Ascending(new_left_nums + [i]);
          assert Ascending(Inorder(t));
          assert BST(t);
        } else {
          LemmaBinarySearchSubtree(i, left, right);
          tmp := InsertBST(right, x);
          t := Node(i, left, tmp);
          ghost var right_nums := Inorder(right);
          ghost var left_nums := Inorder(left);
          ghost var all_nums := Inorder(t0);
          assert all_nums == left_nums + [i] + right_nums;
          assert all_nums[|left_nums|] == i;
          assert all_nums[|left_nums| + 1..] == right_nums;
          assert Ascending(right_nums);
          assert Ascending(left_nums);
          assert Ascending(left_nums + [i] + right_nums);
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: (0 <= j < k < |left_nums| ==> all_nums[j] < all_nums[k]) && (0 <= j < k < |left_nums| ==> all_nums[k] < i) && (0 <= j < k < |left_nums| ==> i < x);
          ghost var new_all_nums := Inorder(t);
          ghost var new_right_nums := Inorder(tmp);
          assert new_all_nums == left_nums + [i] + new_right_nums;
          assert Ascending(left_nums + [i]);
          assert Ascending(new_right_nums);
          assert NumbersInSequence(new_right_nums) == NumbersInSequence(right_nums) + {x};
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: 0 <= j < k < |all_nums| ==> all_nums[j] < all_nums[k];
          assert forall j: int, k: int {:trigger all_nums[k], all_nums[j]} :: (|left_nums| < j < k < |all_nums| ==> all_nums[|left_nums|] < all_nums[j]) && (|left_nums| < j < k < |all_nums| ==> all_nums[j] < all_nums[k]);
          assert all_nums[|left_nums|] == i;
          assert left_nums == all_nums[..|left_nums|];
          assert NumbersInSequence(new_right_nums) == NumbersInSequence(all_nums[|left_nums| + 1..]) + {x};
          assert forall j: int, k: int {:trigger right_nums[k], right_nums[j]} :: (0 <= j < k < |right_nums| ==> i < right_nums[j]) && (0 <= j < k < |right_nums| ==> right_nums[j] < right_nums[k]);
          assert x > i;
          assert forall j: int {:trigger j in NumbersInSequence(new_right_nums)} :: j in NumbersInSequence(new_right_nums) ==> j > i;
          assert forall j: int {:trigger j in new_right_nums} {:trigger j in NumbersInSequence(new_right_nums)} :: j in NumbersInSequence(new_right_nums) <==> j in new_right_nums;
          assert forall j: int, k: int {:trigger new_right_nums[k], new_right_nums[j]} :: 0 <= j < k < |new_right_nums| ==> new_right_nums[j] < new_right_nums[k];
          assert x > i;
          assert forall j: int {:trigger new_right_nums[j]} :: 0 <= j < |new_right_nums| ==> new_right_nums[j] > i;
          assert Ascending(Inorder(t));
          assert BST(t);
        }
      }
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
