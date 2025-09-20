// dafny-synthesis_task_id_432.dfy

method MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
  decreases a, b
{
  median := 2;
}
