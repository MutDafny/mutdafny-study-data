// dafny-synthesis_task_id_304.dfy

method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
  decreases l, n, index
{
  element := l[(index - n + |l|) / |l|];
}
