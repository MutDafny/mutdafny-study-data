// CVS-handout1_tmp_tmptm52no3k_1.dfy

function sum(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j - i
{
  if i == j then
    0
  else
    a[i] + sum(a, i + 1, j)
}

method query(a: array<int>, i: int, j: int)
    returns (res: int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
  decreases a, i, j
{
  res := 0;
  var k := i;
  while k < j
    invariant i <= k <= j <= a.Length
    invariant res + sum(a, k, j) == sum(a, i, j)
    decreases j - k
  {
    res := res + a[k];
    k := k + 1;
  }
}

predicate is_prefix_sum_for(a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
  decreases {c, a}, a, c
{
  forall i: int, _t#0: int {:trigger a[i], c[_t#0]} {:trigger c[i], c[_t#0]} | _t#0 == i + 1 :: 
    0 <= i &&
    i < a.Length ==>
      c[_t#0] == c[i] + a[i]
}

lemma /*{:_inductionTrigger c[j], c[i], is_prefix_sum_for(a, c)}*/ /*{:_inductionTrigger c[j], c[i], a.Length}*/ /*{:_induction a, i, j}*/ aux(a: array<int>, c: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  requires is_prefix_sum_for(a, c)
  ensures forall k: int {:trigger c[k]} {:trigger sum(a, k, j)} {:trigger sum(a, i, k)} :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k]
  decreases j - i
{
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int)
    returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  ensures r == sum(a, i, j)
  decreases a, c, i, j
{
  aux(a, c, i, j);
  r := c[j] - c[i];
}

method Main()
{
  var x := new int[10];
  var y := sum(x, 0, x.Length);
  x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
  var c := new int[11];
  c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
}
