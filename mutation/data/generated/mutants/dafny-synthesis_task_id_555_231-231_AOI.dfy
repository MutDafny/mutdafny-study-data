// dafny-synthesis_task_id_555.dfy

method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
  requires n >= 0
  ensures diff == n * n * (n + 1) * (n + 1) / 4 - n * (n + 1) / 2
  decreases n
{
  var sumCubes := 0;
  var sumNumbers := 0;
  for i: int := 1 to n + -1
    invariant 0 <= i <= n + 1
    invariant sumCubes == (i - 1) * (i - 1) * i * i / 4
    invariant sumNumbers == (i - 1) * i / 2
  {
    sumCubes := sumCubes + i * i * i;
    sumNumbers := sumNumbers + i;
  }
  diff := sumCubes - sumNumbers;
}
