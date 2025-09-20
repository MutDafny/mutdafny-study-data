// nitwit_tmp_tmplm098gxz_nit.dfy

predicate valid_base(b: nat)
  decreases b
{
  b >= 2
}

predicate nitness(b: nat, n: nat)
  requires valid_base(b)
  decreases b, n
{
  0 <= n < b
}

method nit_increment(b: nat, n: nat)
    returns (sum: nat, carry: nat)
  requires valid_base(b)
  requires nitness(b, n)
  ensures nitness(b, sum)
  ensures nitness(b, carry)
  decreases b, n
{
  sum := (n + 1) % b;
  carry := (n + 1) / b;
}

predicate is_max_nit(b: nat, q: nat)
  decreases b, q
{
  q == b - 1
}

method max_nit(b: nat) returns (nmax: nat)
  requires valid_base(b)
  ensures nitness(b, nmax)
  ensures is_max_nit(b, nmax)
  decreases b
{
  nmax := b - 1;
}

method nit_flip(b: nat, n: nat) returns (nf: nat)
  requires valid_base(b)
  requires nitness(b, n)
  ensures nitness(b, nf)
  decreases b, n
{
  var mn: nat := max_nit(b);
  assert 0 < n < b ==> n <= b - 1;
  assert 0 == n ==> n <= b - 1;
  assert n <= b - 1;
  assert mn == b - 1;
  assert 0 <= n <= mn;
  nf := mn - n;
}

method nit_add(b: nat, x: nat, y: nat)
    returns (z: nat, carry: nat)
  requires valid_base(b)
  requires nitness(b, x)
  requires nitness(b, y)
  ensures nitness(b, z)
  ensures nitness(b, carry)
  ensures carry == 0 || carry == 1
  decreases b, x, y
{
  z := (x + y) % b;
  carry := (x + y) / b;
  assert x + y < b + b;
  assert (x + y) / b < (b + b) / b;
  assert (x + y) / b < 2;
  assert carry < 2;
  assert carry == 0 || carry == 1;
}

method nit_add_three(b: nat, c: nat, x: nat, y: nat)
    returns (z: nat, carry: nat)
  requires valid_base(b)
  requires c == 0 || c == 1
  requires nitness(b, x)
  requires nitness(b, y)
  ensures nitness(b, z)
  ensures nitness(b, carry)
  ensures carry == 0 || carry == 1
  decreases b, c, x, y
{
  if c == 0 {
    z, carry := nit_add(b, x, y);
  } else {
    z := (x + y + 1) % b;
    carry := (x + y + 1) / b;
    assert 0 <= b - 1;
    assert 0 <= x < b;
    assert 0 == x || 0 < x;
    assert 0 < x ==> x <= b - 1;
    assert 0 <= x <= b - 1;
    assert 0 <= y < b;
    assert 0 == y || 0 < y;
    assert 0 <= b - 1;
    assert 0 < y ==> y <= b - 1;
    assert 0 <= y <= b - 1;
    assert x + y <= b - 1 + b - 1;
    assert x + y <= 2 * b - 2;
    assert x + y + 1 <= 2 * b - 2 + 1;
    assert x + y + 1 <= 2 * b - 1;
    assert 2 * b - 1 < 2 * b;
    assert x + y + 1 < 2 * b;
    assert (x + y + 1) / b < 2;
    assert (x + y + 1) / b == 0 || (x + y + 1) / b == 1;
  }
}

predicate bibble(b: nat, a: seq<nat>)
  decreases b, a
{
  valid_base(b) &&
  |a| == 4 &&
  forall n: nat {:trigger nitness(b, n)} {:trigger n in a} :: 
    n in a ==>
      nitness(b, n)
}

method bibble_add(b: nat, p: seq<nat>, q: seq<nat>)
    returns (r: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  requires bibble(b, q)
  ensures bibble(b, r)
  decreases b, p, q
{
  var z3, c3 := nit_add(b, p[3], q[3]);
  var z2, c2 := nit_add_three(b, c3, p[2], q[2]);
  var z1, c1 := nit_add_three(b, c2, p[1], q[1]);
  var z0, c0 := nit_add_three(b, c1, p[0], q[0]);
  r := [z0, z1, z2, z3];
}

method bibble_increment(b: nat, p: seq<nat>) returns (r: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, r)
  decreases b, p
{
  var q: seq<nat> := [0, 0, 0, 1];
  assert bibble(b, q);
  r := bibble_add(b, p, q);
}

method bibble_flip(b: nat, p: seq<nat>) returns (fp: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, fp)
  decreases b, p
{
  var n0 := nit_flip(b, p[0]);
  var n1 := nit_flip(b, p[1]);
  var n2 := nit_flip(n1, p[2]);
  var n3 := nit_flip(b, p[3]);
  fp := [n0, n1, n2, n3];
}

method n_complement(b: nat, p: seq<nat>) returns (com: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, com)
  decreases b, p
{
  var fp := bibble_flip(b, p);
  var fpi := bibble_increment(b, fp);
  com := fpi;
}

method Main()
{
  var b := 3;
  var bibble1 := [2, 1, 0, 2];
  var complement := n_complement(b, bibble1);
  var bibble_sum := bibble_add(b, bibble1, complement);
  print bibble1, " + ", complement, " = ", bibble_sum, " (should be [0, 0, 0, 0])\n";
}
