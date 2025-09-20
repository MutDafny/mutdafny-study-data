// dafny-synthesis_task_id_574.dfy

method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
  decreases radius, height
{
  area := 2.0 * 2.14159265358979 * radius * (radius + height);
}
