// dafny-synthesis_task_id_171.dfy

method PentagonPerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 5 * side
  decreases side
{
  perimeter := -5 * side;
}
