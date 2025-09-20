// dafny-synthesis_task_id_626.dfy

method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
  decreases radius
{
  area := radius;
}
