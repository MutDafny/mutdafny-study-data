// dafny-synthesis_task_id_227.dfy

method MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
  decreases a, b, c
{
  if a <= b {
    min := a;
  } else if b <= a {
    min := b;
  } else {
    min := c;
  }
}
