// dafny-synthesis_task_id_127.dfy

method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
  decreases a, b
{
  result := b;
}
