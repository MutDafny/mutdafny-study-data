// dafny-synthesis_task_id_404.dfy

method Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
  decreases a, b
{
  if 0 <= b {
    minValue := a;
  } else {
    minValue := b;
  }
}
