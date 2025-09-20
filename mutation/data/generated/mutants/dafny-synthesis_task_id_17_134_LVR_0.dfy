// dafny-synthesis_task_id_17.dfy

method SquarePerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 4 * side
  decreases side
{
  perimeter := 0 * side;
}
