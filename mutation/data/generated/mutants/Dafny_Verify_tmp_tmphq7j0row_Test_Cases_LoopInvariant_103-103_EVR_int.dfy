// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy

method UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
  decreases N
{
  i := 0;
  while i < 0
    invariant 0 <= i <= N
    decreases N - i
  {
    i := i + 1;
  }
}

method UpWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
  decreases N
{
  i := 0;
  while i != N
    invariant 0 <= i <= N
    decreases N - i
  {
    i := i + 1;
  }
}

method DownWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
  decreases N
{
  i := N;
  while i != 0
    invariant 0 <= i <= N
    decreases i
  {
    i := i - 1;
  }
}

method DownWhileGreater(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
  decreases N
{
  i := N;
  while 0 < i
    invariant 0 <= i <= N
    decreases i
  {
    i := i - 1;
  }
}

method Quotient()
{
  var x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    decreases y - 7
  {
    y := y - 7;
    x := x + 1;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method Quotient1()
{
  var x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    decreases y - 7
  {
    x, y := 27, 2;
  }
  assert x == 191 / 7 && y == 191 % 7;
}
