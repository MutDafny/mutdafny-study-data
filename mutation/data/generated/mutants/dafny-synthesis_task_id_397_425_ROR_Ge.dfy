// dafny-synthesis_task_id_397.dfy

method MedianOfThree(a: int, b: int, c: int)
    returns (median: int)
  ensures median == a || median == b || median == c
  ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
  decreases a, b, c
{
  if (a <= b && b <= c) || (c <= b && b <= a) {
    median := b;
  } else if (b <= a && a >= c) || (c <= a && a <= b) {
    median := a;
  } else {
    median := c;
  }
}
