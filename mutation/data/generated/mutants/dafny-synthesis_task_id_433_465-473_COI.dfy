// dafny-synthesis_task_id_433.dfy

method IsGreater(n: int, a: array<int>) returns (result: bool)
  requires a != null
  ensures result ==> forall i: int {:trigger a[i]} :: 0 <= i < a.Length ==> n > a[i]
  ensures !result ==> exists i: int {:trigger a[i]} :: 0 <= i < a.Length && n <= a[i]
  decreases n, a
{
  result := true;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result ==> forall k: int {:trigger a[k]} :: 0 <= k < i ==> n > a[k]
    invariant !result ==> exists k: int {:trigger a[k]} :: 0 <= k < i && n <= a[k]
    decreases a.Length - i
  {
    if !(n <= a[i]) {
      result := false;
      break;
    }
    i := i + 1;
  }
}
