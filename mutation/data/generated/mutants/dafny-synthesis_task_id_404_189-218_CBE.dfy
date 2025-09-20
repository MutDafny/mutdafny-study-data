// dafny-synthesis_task_id_404.dfy

method Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
  decreases a, b
{
  minValue := b;
}
