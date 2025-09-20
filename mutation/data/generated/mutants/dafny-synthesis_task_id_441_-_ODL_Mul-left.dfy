// dafny-synthesis_task_id_441.dfy

method CubeSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 6 * size * size
  decreases size
{
  area := size;
}
