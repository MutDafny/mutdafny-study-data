// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_examples_simpleMultiplication.dfy

method Foo(y: int, x: int) returns (z: int)
  requires 0 <= y
  ensures z == x * y
  decreases y, x
{
  var a: int := 0;
  z := 0;
  while a != y
    invariant 0 <= a <= y
    invariant z == a * x
    decreases y - a
  {
    z := z + x;
    a := a + 1;
  }
  return z;
}

function stringToSet(s: string): (r: set<char>)
  ensures forall x: int {:trigger s[x]} :: 0 <= x < |s| ==> s[x] in r
  decreases s
{
  set x: int {:trigger s[x]} | 0 <= x < |s| :: s[x]
}

method Main()
{
}
