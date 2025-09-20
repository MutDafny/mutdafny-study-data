// dafny-synthesis_task_id_58.dfy

method HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
  decreases a, b
{
  result := (a < 0 && b > 0) || a > 0 || b < 0;
}
