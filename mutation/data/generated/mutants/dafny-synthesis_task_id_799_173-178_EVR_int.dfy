// dafny-synthesis_task_id_799.dfy

method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d as bv6) | (n >> (32 - d) as bv6)
  decreases n, d
{
  result := (n << d as bv6) | (n >> 0 as bv6);
}
