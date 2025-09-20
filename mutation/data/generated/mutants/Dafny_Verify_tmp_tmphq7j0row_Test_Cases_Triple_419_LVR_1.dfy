// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method Triple(x: int) returns (r: int)
  decreases x
{
  var y := 2 * x;
  r := x + y;
  assert r == 3 * x;
}

method TripleIf(x: int) returns (r: int)
  decreases x
{
  if x == 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
  assert r == 3 * x;
}

method TripleOver(x: int) returns (r: int)
  decreases x
{
  if {
    case x < 18 =>
      var a, b := 2 * x, 4 * x;
      r := (a + b) / 2;
    case 1 <= x =>
      var y := 2 * x;
      r := x + y;
  }
  assert r == 3 * x;
}

method TripleConditions(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3 * x
  decreases x
{
  var y := x / 2;
  r := 6 * y;
  assert r == 3 * x;
}

method Caller()
{
  var t := TripleConditions(18);
  assert t < 100;
}
