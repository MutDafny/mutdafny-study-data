// Clover_multi_return.dfy

method MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
  decreases x, y
{
  less := x - y;
  more := x + y;
}
