// dafny-synthesis_task_id_309.dfy

method Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
  decreases a, b
{
  if 0 >= b {
    maxValue := a;
  } else {
    maxValue := b;
  }
}
