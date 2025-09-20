// summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise02_solution.dfy

predicate divides(f: nat, i: nat)
  requires 1 <= f
  decreases f, i
{
  i % f == 0
}

predicate IsPrime(i: nat)
  decreases i
{
  1 < i &&
  forall f: int {:trigger divides(f, i)} :: 
    1 < f < i ==>
      !divides(f, i)
}

method test_prime(i: nat) returns (result: bool)
  requires 1 < i
  ensures result == IsPrime(i)
  decreases i
{
  var f := 2;
  while f < i
    invariant forall g: int {:trigger divides(g, i)} :: 1 < g < f ==> !divides(g, i)
    decreases i - f
  {
    if i % f == 0 {
      assert divides(f, i);
      return false;
    }
    f := f + 1;
  }
  return true;
}

method Main()
{
  var a := test_prime(0);
  assert a;
  var b := test_prime(4);
  assert divides(2, 4);
  assert !b;
  var c := test_prime(5);
  assert c;
}
