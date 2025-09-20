// dafny-synthesis_task_id_804.dfy

predicate IsEven(n: int)
  decreases n
{
  n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
  ensures result <==> exists i: int {:trigger a[i]} :: 0 <= i < a.Length && IsEven(a[i])
  decreases a
{
  result := false;
  for i: int := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> exists k: int {:trigger a[k]} :: 0 <= k < i && IsEven(a[k])
  {
    if IsEven(a[i]) {
      break;
    }
  }
}
