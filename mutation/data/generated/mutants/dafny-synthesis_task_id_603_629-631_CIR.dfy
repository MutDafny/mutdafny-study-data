// dafny-synthesis_task_id_603.dfy

method LucidNumbers(n: int) returns (lucid: seq<int>)
  requires n >= 0
  ensures forall i: int {:trigger lucid[i]} :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
  ensures forall i: int {:trigger lucid[i]} :: 0 <= i < |lucid| ==> lucid[i] <= n
  ensures forall i: int, j: int {:trigger lucid[j], lucid[i]} :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
  decreases n
{
  lucid := [];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k: int {:trigger lucid[k]} :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0
    invariant forall k: int {:trigger lucid[k]} :: 0 <= k < |lucid| ==> lucid[k] <= i - 1
    invariant forall k: int, l: int {:trigger lucid[l], lucid[k]} :: 0 <= k < l < |lucid| ==> lucid[k] < lucid[l]
    decreases n - i
  {
    if i % 3 == 0 {
      lucid := lucid + [];
    }
    i := i + 1;
  }
}
