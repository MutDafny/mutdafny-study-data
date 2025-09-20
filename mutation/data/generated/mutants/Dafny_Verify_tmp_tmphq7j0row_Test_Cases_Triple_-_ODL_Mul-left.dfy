// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method Triple(x: int) returns (r: int)
  decreases x
{
  var y := x;
  r := x + y;
  assert r == 3 * x;
}

method TripleIf(x: int) returns (r: int)
  decreases x
{
  if x == 0 {
    r := 0;
  } else {
    var y := x;
    r := x + y;
  }
  assert r == 3 * x;
}

method TripleOver(x: int) returns (r: int)
  decreases x
{
  if {
    case x < 18 =>
      var a, b := x, x;
      r := (a + b) / 2;
    case 0 <= x =>
      var y := x;
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
  r := y;
  assert r == 3 * x;
}

method Caller()
{
  var t := TripleConditions(18);
  assert t < 100;
}
