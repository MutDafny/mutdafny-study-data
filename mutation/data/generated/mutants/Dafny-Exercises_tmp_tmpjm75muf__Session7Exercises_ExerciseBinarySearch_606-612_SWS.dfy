// Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBinarySearch.dfy

predicate sorted(s: seq<int>)
  decreases s
{
  forall u: int, w: int {:trigger s[w], s[u]} :: 
    0 <= u < w < |s| ==>
      s[u] <= s[w]
}

method binarySearch(v: array<int>, elem: int) returns (p: int)
  requires sorted(v[0 .. v.Length])
  ensures -1 <= p < v.Length
  ensures (forall u: int {:trigger v[u]} :: 0 <= u <= p ==> v[u] <= elem) && forall w: int {:trigger v[w]} :: p < w < v.Length ==> v[w] > elem
  decreases v, elem
{
  var c, f := 0, v.Length - 1;
  p := c - 1;
  while c <= f
    invariant 0 <= c <= v.Length && -1 <= f <= v.Length - 1 && c <= f + 1
    invariant (forall u: int {:trigger v[u]} :: 0 <= u < c ==> v[u] <= elem) && forall w: int {:trigger v[w]} :: f < w < v.Length ==> v[w] > elem
    decreases f - c
  {
    var m := (c + f) / 2;
    if v[m] <= elem {
      c := m + 1;
    } else {
      f := m - 1;
    }
  }
}

method search(v: array<int>, elem: int) returns (b: bool)
  requires sorted(v[0 .. v.Length])
  ensures b == (elem in v[0 .. v.Length])
  decreases v, elem
{
  var p := binarySearch(v, elem);
  if p == -1 {
    b := false;
  } else {
    b := v[p] == elem;
  }
}

method {:tailrecursion false} binarySearchRec(v: array<int>, elem: int, c: int, f: int)
    returns (p: int)
  requires sorted(v[0 .. v.Length])
  requires 0 <= c <= f + 1 <= v.Length
  requires forall k: int {:trigger v[k]} :: 0 <= k < c ==> v[k] <= elem
  requires forall k: int {:trigger v[k]} :: f < k < v.Length ==> v[k] > elem
  ensures -1 <= p < v.Length
  ensures (forall u: int {:trigger v[u]} :: 0 <= u <= p ==> v[u] <= elem) && forall w: int {:trigger v[w]} :: p < w < v.Length ==> v[w] > elem
  decreases f - c
{
  if c == f + 1 {
    p := c - 1;
  } else {
    var m := (c + f) / 2;
    if v[m] <= elem {
      p := binarySearchRec(v, elem, m + 1, f);
    } else {
      p := binarySearchRec(v, elem, c, m - 1);
    }
  }
}

method otherbSearch(v: array<int>, elem: int)
    returns (b: bool, p: int)
  requires sorted(v[0 .. v.Length])
  ensures 0 <= p <= v.Length
  ensures b == (elem in v[0 .. v.Length])
  ensures b ==> p < v.Length && v[p] == elem
  ensures !b ==> (forall u: int {:trigger v[u]} :: 0 <= u < p ==> v[u] < elem) && forall w: int {:trigger v[w]} :: p <= w < v.Length ==> v[w] > elem
  decreases v, elem
{
  p := binarySearch(v, elem);
  if p == -1 {
    b := false;
    p := p + 1;
  } else {
    b := v[p] == elem;
    p := p + if b then 0 else 1;
  }
}
