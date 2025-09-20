// Clover_multi_return.dfy

method MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
  decreases x, y
{
  more := y;
  less := x - y;
}
