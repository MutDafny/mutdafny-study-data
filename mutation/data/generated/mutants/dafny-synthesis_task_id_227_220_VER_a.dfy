// dafny-synthesis_task_id_227.dfy

method MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
  decreases a, b, c
{
  if a <= b && a <= c {
    min := a;
  } else if a <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}
