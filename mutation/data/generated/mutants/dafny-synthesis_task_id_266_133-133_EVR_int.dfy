// dafny-synthesis_task_id_266.dfy

method LateralSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 4 * size * size
  decreases size
{
  area := 4 * 0 * size;
}
