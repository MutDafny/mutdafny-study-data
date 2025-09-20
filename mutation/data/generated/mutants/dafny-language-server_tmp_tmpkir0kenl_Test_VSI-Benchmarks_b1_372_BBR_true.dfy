// dafny-language-server_tmp_tmpkir0kenl_Test_VSI-Benchmarks_b1.dfy

method Add(x: int, y: int) returns (r: int)
  ensures r == x + y
  decreases x, y
{
  r := x;
  if true {
    var n := y;
    while n != 0
      invariant r == x + y - n && 0 <= -n
      decreases if n <= 0 then 0 - n else n - 0
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      invariant r == x + y - n && 0 <= n
      decreases if n <= 0 then 0 - n else n - 0
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method Mul(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x == 0 {
    r := 0;
  } else if x < 0 {
    r := Mul(-x, y);
    r := -r;
  } else {
    r := Mul(x - 1, y);
    r := Add(r, y);
  }
}

method Main()
{
  TestAdd(3, 180);
  TestAdd(3, -180);
  TestAdd(0, 1);
  TestMul(3, 180);
  TestMul(3, -180);
  TestMul(180, 3);
  TestMul(-180, 3);
  TestMul(0, 1);
  TestMul(1, 0);
}

method TestAdd(x: int, y: int)
  decreases x, y
{
  print x, " + ", y, " = ";
  var z := Add(x, y);
  print z, "\n";
}

method TestMul(x: int, y: int)
  decreases x, y
{
  print x, " * ", y, " = ";
  var z := Mul(x, y);
  print z, "\n";
}
