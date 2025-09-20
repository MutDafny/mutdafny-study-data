// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week1_7_MaxSum.dfy

method MaxSum(x: int, y: int)
    returns (s: int, m: int)
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
  decreases x, y
{
  s := x + y;
  if x > y {
    m := x;
  } else if y > x {
    m := y;
  } else {
    m := x;
  }
  assert m >= y;
}

method Main()
{
  var m, n := 3, 5;
  var a, b := MaxSum(m, n);
  print "Search return a is ", a, ",,,,, b is ", b, "\n";
}
