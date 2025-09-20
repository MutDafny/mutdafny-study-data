// dafny-synthesis_task_id_292.dfy

method Quotient(a: int, b: int) returns (result: int)
  requires b != 0
  ensures result == a / b
  decreases a, b
{
  result := a / a;
}
