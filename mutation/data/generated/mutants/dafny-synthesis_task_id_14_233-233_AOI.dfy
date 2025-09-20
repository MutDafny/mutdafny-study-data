// dafny-synthesis_task_id_14.dfy

method TriangularPrismVolume(base: int, height: int, length: int)
    returns (volume: int)
  requires base > 0
  requires height > 0
  requires length > 0
  ensures volume == base * height * length / 2
  decreases base, height, length
{
  volume := base * -height * length / 2;
}
