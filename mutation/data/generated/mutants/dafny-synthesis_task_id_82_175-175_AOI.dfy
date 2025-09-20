// dafny-synthesis_task_id_82.dfy

method SphereVolume(radius: real) returns (volume: real)
  requires radius > 0.0
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
  decreases radius
{
  volume := 4.0 / -3.0 * 3.1415926535 * radius * radius * radius;
}
