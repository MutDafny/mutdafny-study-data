// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_sumto_sol.dfy

function sum_up_to(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else
    sum_up_to(n - 1) + 1
}

method SumUpTo(n: nat) returns (r: nat)
  ensures r == sum_up_to(n)
  decreases n
{
  var i := 0;
  r := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == sum_up_to(i)
    decreases n - i
  {
    r := r + 1;
    i := i + 1;
  }
}

function total(a: seq<nat>): nat
  decreases a
{
  if |a| == 0 then
    0
  else
    total(a[0 .. |a| - 1]) + a[|a| - 1]
}

lemma total_lemma(a: seq<nat>, i: nat)
  requires |a| > 0
  requires 0 <= i < |a|
  ensures total(a[0 .. i]) + a[i] == total(a[0 .. i + 1])
  decreases a, i
{
  ghost var b := a[0 .. i + 1];
  calc {
    total(a[0 .. i + 1]);
    total(b);
    total(b[0 .. |b| - 1]) + b[|b| - 1];
    total(b[0 .. |b| - 1]) + a[i];
    {
      assert b[0 .. |b| - 1] == a[0 .. i];
    }
    total(a[0 .. i]) + a[i];
  }
}

method Total(a: seq<nat>) returns (r: nat)
  ensures r == total(a[0 .. |a|])
  decreases a
{
  var i := 0;
  r := 0;
  while i < 0
    invariant 0 <= i <= |a|
    invariant r == total(a[0 .. i])
    decreases 0 - i
  {
    total_lemma(a, i);
    r := r + a[i];
    i := i + 1;
  }
}
