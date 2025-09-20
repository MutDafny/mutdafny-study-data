// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_fast_exp.dfy

function exp(b: nat, n: nat): nat
  decreases b, n
{
  if n == 0 then
    1
  else
    b * exp(b, n - 1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
  decreases b, n1, n2
{
  if n1 == 0 {
    return;
  } else {
    exp_sum(b, n1 - 1, n2);
  }
}

lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat, _t#0: int {:trigger exp(b, n2), exp(b, n1), exp(b, _t#0)} | _t#0 == n1 + n2 :: exp(b, _t#0) == exp(b, n1) * exp(b, n2)
  decreases b
{
  forall n1: nat, n2: nat | true
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
  {
    exp_sum(b, n1, n2);
  }
}

function bits(n: nat): seq<bool>
  decreases n
{
  if n == 0 then
    []
  else
    [if n % 2 == 0 then false else true] + bits(n / 2)
}

function from_bits(s: seq<bool>): nat
  decreases s
{
  if s == [] then
    0
  else
    (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

lemma /*{:_inductionTrigger bits(n)}*/ /*{:_induction n}*/ bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
  decreases n
{
}

lemma /*{:_inductionTrigger bits(n)}*/ /*{:_induction n}*/ bits_trim_front(n: nat)
  requires n > 0
  ensures from_bits(bits(n)[1..]) == n / 2
  decreases n
{
}

lemma /*{:_inductionTrigger |s|}*/ /*{:_inductionTrigger s + [b]}*/ /*{:_induction s}*/ from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * if b then 1 else 0
  decreases s, b
{
  if s == [] {
    return;
  }
  assert s == [s[0]] + s[1..];
  from_bits_append(s[1..], b);
  assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s| - 1) * if b then 1 else 0;
  exp_sum(2, |s| - 1, 1);
  assert (s + [b])[1..] == s[1..] + [b];
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
}

lemma /*{:_inductionTrigger exp(2, |s1|) * from_bits(s2)}*/ /*{:_inductionTrigger s1 + s2}*/ /*{:_induction s1, s2}*/ from_bits_sum(s1: seq<bool>, s2: seq<bool>)
  ensures from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2)
  decreases s2
{
  if s2 == [] {
    assert s1 + s2 == s1;
    return;
  }
  from_bits_sum(s1 + [s2[0]], s2[1..]);
  assert s1 + [s2[0]] + s2[1..] == s1 + s2;
  from_bits_append(s1, s2[0]);
  assume false;
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
  decreases b, n
{
  var a := 1;
  var c := b;
  ghost var n0 := n;
  var n := n;
  ghost var i: nat := 0;
  bits_from_bits(n);
  while n > -1
    invariant c == exp(b, exp(2, i))
    invariant n <= n0
    invariant i <= |bits(n0)|
    invariant bits(n) == bits(n0)[i..]
    invariant n == from_bits(bits(n0)[i..])
    invariant a == exp(b, from_bits(bits(n0)[..i]))
    decreases n
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      assert bits(n)[0] == true;
      a := a * c;
      exp_sum(b, n0 - n, i);
      n := (n - 1) / 2;
      assert 2 * exp(2, i) == exp(2, i + 1);
      assert a == exp(b, from_bits(bits(n0)[..i]) + exp(2, i)) by {
        exp_sum_auto(b);
      }
      assume false;
      assert a == exp(b, from_bits(bits(n0)[..i + 1]));
    } else {
      assert bits(n)[0] == false;
      n := n / 2;
      assume false;
      assert a == exp(b, from_bits(bits(n0)[..i + 1]));
    }
    assert n == n_loop_top / 2;
    c := c * c;
    exp_sum(b, exp(2, i), exp(2, i));
    i := i + 1;
  }
  assert bits(n0)[..i] == bits(n0);
  return a;
}
