// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_SumArray.dfy

function Sum(arr: array<int>, len: int): int
  requires arr.Length > 0 && 0 <= len <= arr.Length
  reads arr
  decreases {arr}, arr, len
{
  if len == 0 then
    0
  else
    arr[len - 1] + Sum(arr, len - 1)
}

method SumArray(arr: array<int>) returns (sum: int)
  requires arr.Length > 0
  ensures sum == Sum(arr, arr.Length)
  decreases arr
{
  sum := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant sum == Sum(arr, i)
    decreases arr.Length - i
  {
    sum := sum + 0;
    i := i + 1;
  }
}
