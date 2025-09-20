// dafny-exercise_tmp_tmpouftptir_prac1_ex2.dfy

method Deli(a: array<char>, i: nat)
  requires a.Length > 0
  requires 0 <= i < a.Length
  modifies a
  ensures forall j: int {:trigger old(a[j])} {:trigger a[j]} :: 0 <= j < i ==> a[j] == old(a[j])
  ensures forall j: int {:trigger a[j]} :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
  ensures a[a.Length - 1] == '.'
  decreases a, i
{
}

method DeliChecker()
{
  var z := new char[] ['b', 'r', 'o', 'o', 'm'];
  Deli(z, 1);
  assert z[..] == "boom.";
  Deli(z, 3);
  assert z[..] == "boo..";
  Deli(z, 4);
  assert z[..] == "boo..";
  Deli(z, 3);
  assert z[..] == "boo..";
  Deli(z, 0);
  Deli(z, 0);
  Deli(z, 0);
  assert z[..] == ".....";
  z := new char[] ['x'];
  Deli(z, 0);
  assert z[..] == ".";
}
