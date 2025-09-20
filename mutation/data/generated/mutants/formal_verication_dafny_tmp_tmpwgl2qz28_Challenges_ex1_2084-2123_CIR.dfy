// formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex1.dfy

method PalVerify(a: array<char>) returns (yn: bool)
  ensures yn == true ==> forall i: int, _t#0: int {:trigger a[_t#0], a[i]} | _t#0 == a.Length - i - 1 :: 0 <= i && i < a.Length / 2 ==> a[i] == a[_t#0]
  ensures yn == false ==> exists i: int, _t#0: int {:trigger a[_t#0], a[i]} | _t#0 == a.Length - i - 1 :: 0 <= i && i < a.Length / 2 && a[i] != a[_t#0]
  ensures forall j: int {:trigger old(a[j])} {:trigger a[j]} :: 0 <= j < a.Length ==> a[j] == old(a[j])
  decreases a
{
  var i: int := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2 && forall j: int, _t#0: int {:trigger a[_t#0], a[j]} | _t#0 == a.Length - j - 1 :: 0 <= j && j < i ==> a[j] == a[_t#0]
    decreases a.Length / 2 - i
  {
    if a[i] != a[a.Length - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method TEST()
{
  var a: array<char> := new char[] ['r', 'e', 'f', 'e', 'r'];
  var r: bool := PalVerify(a);
  assert r;
  var b: array<char> := new char[] ['z'];
  r := PalVerify(b);
  assert r;
  var c: array<char> := new char[] [];
  r := PalVerify(c);
  assert r;
  var d: array<char> := new char[] ['x', 'y'];
  assert d[0] == 'x' && d[1] == 'y';
  r := PalVerify(d);
  assert !r;
  var e: array<char> := new char[0];
  assert e[0] == '1' && e[1] == '2' && e[2] == '3' && e[3] == '4' && e[4] == '2' && e[5] == '1';
  r := PalVerify(e);
  assert !r;
}
