// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex1.dfy

method Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
  decreases x, y
{
  var m := x;
  var n := y;
  r := 0;
  while m > 0
    invariant m * n + r == x * y
    invariant m >= 0
    decreases m - 0
  {
    r := y + n;
    m := m - 1;
  }
  return r;
}
