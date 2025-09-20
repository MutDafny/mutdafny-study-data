// assertive-programming-assignment-1_tmp_tmp3h_cj44u_ProdAndCount.dfy

method Main()
{
  var q := [7, -2, 3, -2];
  var p, c := ProdAndCount(q, -2);
  print "The product of all positive elements in [7,-2,3,-2] is ";
  print p;
  assert p == RecursivePositiveProduct(q) == 21;
  print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
  print c;
  assert c == RecursiveCount(-2, q) == 2 by {
    calc {
      RecursiveCount(-2, q);
    ==
      {
        assert q[3] == -2;
        AppendOne(q, 3);
      }
      1 + RecursiveCount(-2, q[..3]);
    ==
      {
        assert q[2] != -2;
        AppendOne(q, 2);
      }
      1 + RecursiveCount(-2, q[..2]);
    ==
      {
        assert q[1] == -2;
        AppendOne(q, 1);
      }
      1 + 1 + RecursiveCount(-2, q[..1]);
    ==
      {
        assert q[0] != -2;
        AppendOne(q, 0);
      }
      1 + 1 + RecursiveCount(-2, q[..0]);
    }
  }
}

lemma AppendOne<T>(q: seq<T>, n: nat)
  requires n < |q|
  ensures q[..n] + [q[n]] == q[..n + 1]
  decreases q, n
{
}

function RecursivePositiveProduct(q: seq<int>): int
  decreases |q|
{
  if q == [] then
    1
  else if q[0] <= 0 then
    RecursivePositiveProduct(q[1..])
  else
    q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
  decreases |q|
{
  if q == [] then
    0
  else if q[|q| - 1] == key then
    1 + RecursiveCount(key, q[..|q| - 1])
  else
    RecursiveCount(key, q[..|q| - 1])
}

method ProdAndCount(q: seq<int>, key: int)
    returns (prod: int, count: nat)
  ensures prod == RecursivePositiveProduct(q)
  ensures count == RecursiveCount(key, q)
  decreases q, key
{
  prod := 0;
  count := 0;
  var size := |q|;
  var i := 0;
  var curr := 0;
  while i < size
    invariant 0 <= i <= size && count == RecursiveCount(key, q[..i]) && prod == RecursivePositiveProduct(q[..i])
    decreases size - i
  {
    Lemma_Count_Inv(q, i, count, key);
    Lemma_Prod_Inv(q, i, prod);
    curr := q[i];
    if curr > 0 {
      prod := prod * curr;
    }
    if curr == key {
      count := count + 1;
    }
    i := i + 1;
  }
  Lemma_Count_Finish(q, i, count, key);
  Lemma_Prod_Finish(q, i, prod);
}

function county(elem: int, key: int): int
  decreases elem, key
{
  if elem == key then
    1
  else
    0
}

function prody(elem: int): int
  decreases elem
{
  if elem <= 0 then
    1
  else
    elem
}

lemma /*{:_inductionTrigger county(q[i], key)}*/ /*{:_inductionTrigger RecursiveCount(key, q[..i])}*/ /*{:_induction key}*/ Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
  requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
  ensures 0 <= i + 1 <= |q| && county(q[i], key) + count == RecursiveCount(key, q[..i + 1])
  decreases q, i, count, key
{
  assert q[..i + 1] == q[..i] + [q[i]];
  ghost var q1 := q[..i + 1];
  calc {
    RecursiveCount(key, q[..i + 1]);
  ==
    if q1 == [] then 0 else if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      assert q1 != [];
    }
    if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      KibutzLaw1(q1, key, i);
    }
    (if q1[i] == key then 1 else 0) + RecursiveCount(key, q1[..i]);
  ==
    county(q1[i], key) + RecursiveCount(key, q1[..i]);
  ==
    county(q[i], key) + RecursiveCount(key, q[..i]);
  }
}

lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
  requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
  ensures 0 <= i + 1 <= |q| && prody(q[i]) * prod == RecursivePositiveProduct(q[..i + 1])
  decreases q, i, prod
{
  assert q[..i + 1] == q[..i] + [q[i]];
  ghost var q1 := q[..i + 1];
  calc {
    RecursivePositiveProduct(q[..i + 1]);
  ==
    if q1 == [] then 1 else if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    {
      assert q1 != [];
    }
    if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    if q[0] <= 0 then RecursivePositiveProduct(q[1 .. i + 1]) else q[0] * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      PrependProd(q);
    }
    RecursivePositiveProduct(q[..i + 1]);
  ==
    {
      AppendProd(q[..i + 1]);
    }
    prody(q[i]) * RecursivePositiveProduct(q[..i]);
  ==
    prody(q[i]) * prod;
  }
}

lemma /*{:_inductionTrigger RecursiveCount(key, q[..i])}*/ /*{:_induction q, key}*/ Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
  requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
  requires neg_of_guard: i >= |q|
  ensures count == RecursiveCount(key, q)
  decreases q, i, count, key
{
  assert i <= |q| && count == RecursiveCount(key, q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
}

lemma /*{:_inductionTrigger q[..i]}*/ /*{:_inductionTrigger |q|}*/ /*{:_induction q}*/ Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
  requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
  requires neg_of_guard: i >= |q|
  ensures prod == RecursivePositiveProduct(q)
  decreases q, i, prod
{
  assert i <= |q| && prod == RecursivePositiveProduct(q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
}

lemma KibutzLaw1(q: seq<int>, key: int, i: nat)
  requires q != [] && i < |q|
  ensures (if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1])) == (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1])
  decreases q, key, i
{
  if q[|q| - 1] == key {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      1 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  } else {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  }
}

lemma {:verify true} KibutzLaw2(q: seq<int>)
  requires q != []
  ensures (if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..])) == (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..])
  decreases q
{
  if q[0] <= 0 {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  } else {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      q[0] * RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  }
}

lemma /*{:_inductionTrigger RecursiveCount(key, q)}*/ /*{:_induction key, q}*/ AppendCount(key: int, q: seq<int>)
  requires q != []
  ensures RecursiveCount(key, q) == RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key)
  decreases key, q
{
  if |q| == 1 {
    assert RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key) == RecursiveCount(key, q[..0]) + county(q[0], key) == RecursiveCount(key, []) + county(q[0], key) == 0 + county(q[0], key) == county(q[0], key);
    assert RecursiveCount(key, q) == county(q[0], key);
  } else {
    ghost var q1 := q[1..];
    calc {
      RecursiveCount(key, q);
    ==
      if q == [] then 0 else if q[|q| - 1] == key then 1 + RecursiveCount(key, q[..|q| - 1]) else RecursiveCount(key, q[..|q| - 1]);
    ==
      RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key);
    }
  }
}

lemma /*{:_inductionTrigger q[1..]}*/ /*{:_inductionTrigger q[0]}*/ /*{:_induction q}*/ PrependProd(q: seq<int>)
  requires q != []
  ensures RecursivePositiveProduct(q) == prody(q[0]) * RecursivePositiveProduct(q[1..])
  decreases q
{
  calc {
    RecursivePositiveProduct(q);
  ==
    if q == [] then 1 else if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      assert q != [];
    }
    if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1..]);
  }
}

lemma /*{:_inductionTrigger |q|}*/ /*{:_induction q}*/ AppendProd(q: seq<int>)
  requires q != []
  ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1])
  decreases q
{
  if |q| == 1 {
    assert RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]) == RecursivePositiveProduct(q[..0]) * prody(q[0]) == RecursivePositiveProduct([]) * prody(q[0]) == 1 * prody(q[0]) == prody(q[0]);
    assert RecursivePositiveProduct(q) == prody(q[0]);
  } else {
    ghost var q1 := q[1..];
    calc {
      RecursivePositiveProduct(q);
    ==
      prody(q[0]) * RecursivePositiveProduct(q[1..]);
    ==
      {
        assert q1 != [];
        assert |q1| < |q|;
        AppendProd(q1);
      }
      prody(q[0]) * RecursivePositiveProduct(q1[..|q1| - 1]) * prody(q1[|q1| - 1]);
    ==
      {
        assert q1[..|q1| - 1] == q[1 .. |q| - 1];
        assert q1[|q1| - 1] == q[|q| - 1];
      }
      prody(q[0]) * RecursivePositiveProduct(q[1 .. |q| - 1]) * prody(q[|q| - 1]);
    ==
      {
        PrependProd(q[..|q| - 1]);
      }
      RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]);
    }
  }
}
