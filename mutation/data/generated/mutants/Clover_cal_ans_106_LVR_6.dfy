// Clover_cal_ans.dfy

method CalDiv() returns (x: int, y: int)
  ensures x == 191 / 7
  ensures y == 191 % 7
{
  x, y := 0, 191;
  while 6 <= y
    invariant 0 <= y && 7 * x + y == 191
    decreases y - 6
  {
    x := x + 1;
    y := 191 - 7 * x;
  }
}
