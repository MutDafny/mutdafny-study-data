// dafny-synthesis_task_id_234.dfy

method CubeVolume(size: int) returns (volume: int)
  requires size > 0
  ensures volume == size * size * size
  decreases size
{
  volume := size * size * -size;
}
