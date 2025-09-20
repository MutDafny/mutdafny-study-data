// Clover_multi_return.dfy

method MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
  decreases x, y
{
  more := x;
  less := x - y;
}
