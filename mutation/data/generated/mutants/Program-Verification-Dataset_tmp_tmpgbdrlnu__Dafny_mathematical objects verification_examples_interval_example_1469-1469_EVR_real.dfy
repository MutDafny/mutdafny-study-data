// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example.dfy

predicate contains(i: Interval, r: real)
  decreases i, r
{
  i.lo <= r <= i.hi
}

predicate empty(i: Interval)
  decreases i
{
  i.lo > i.hi
}

lemma empty_ok(i: Interval)
  ensures empty(i) <==> !exists r: real {:trigger contains(i, r)} :: contains(i, r)
  decreases i
{
  if empty(i) {
  } else {
    assert contains(i, i.lo);
  }
}

function min(r1: real, r2: real): real
  decreases r1, r2
{
  if r1 < r2 then
    r1
  else
    r2
}

function max(r1: real, r2: real): real
  decreases r1, r2
{
  if r1 > r2 then
    r1
  else
    0.0
}

function intersect(i1: Interval, i2: Interval): Interval
  decreases i1, i2
{
  Interval(max(i1.lo, i2.lo), min(i1.hi, i2.hi))
}

lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r: real {:trigger contains(i2, r)} {:trigger contains(i1, r)} {:trigger contains(intersect(i1, i2), r)} :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
  decreases i1, i2
{
}

predicate overlap(i1: Interval, i2: Interval)
  decreases i1, i2
{
  !empty(intersect(i1, i2))
}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r: real {:trigger contains(i2, r)} {:trigger contains(i1, r)} :: contains(i1, r) && contains(i2, r)
  decreases i1, i2
{
  if overlap(i1, i2) {
    if i1.lo >= i2.lo {
      assert contains(i2, i1.lo);
    } else {
      assert contains(i1, i2.lo);
    }
  }
}

function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
  decreases i1, i2
{
  Interval(min(i1.lo, i2.lo), max(i1.hi, i2.hi))
}

lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r: real {:trigger contains(i2, r)} {:trigger contains(i1, r)} {:trigger contains(union(i1, i2), r)} :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
  decreases i1, i2
{
}

lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
  decreases i1, i2
{
  if i1.lo >= i2.lo {
    r := i1.lo;
  } else {
    r := i2.lo;
  }
}

datatype Interval = Interval(lo: real, hi: real)
