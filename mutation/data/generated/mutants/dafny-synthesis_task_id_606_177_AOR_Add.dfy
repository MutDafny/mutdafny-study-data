// dafny-synthesis_task_id_606.dfy

method DegreesToRadians(degrees: real) returns (radians: real)
  ensures radians == degrees * 3.14159265358979323846 / 180.0
  decreases degrees
{
  radians := degrees * 3.14159265358979323846 + 180.0;
}
