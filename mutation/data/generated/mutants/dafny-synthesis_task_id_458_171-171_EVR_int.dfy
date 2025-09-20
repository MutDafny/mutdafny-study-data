// dafny-synthesis_task_id_458.dfy

method RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
  decreases length, width
{
  area := length * 0;
}
