// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Function.dfy

function Average(a: int, b: int): int
  decreases a, b
{
  (a + b) / 2
}

method TripleConditions(x: int) returns (r: int)
  ensures r == 3 * x
  decreases x
{
  r := 3 * x;
  assert r == 3 * x;
}

method Triple'(x: int) returns (r: int)
  ensures Average(r, 3 * x) == 3 * x
  ensures r == 3 * x
  decreases x
{
  r := 3 * x;
}

method ProveSpecificationsEquivalent(x: int)
  decreases x
{
  var result1 := TripleConditions(x);
  var result2 := x;
  assert result1 == result2;
}
