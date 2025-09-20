// dafny-synthesis_task_id_472.dfy

method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
  requires a.Length > 0
  ensures result <==> exists i: int, _t#0: int {:trigger a[_t#0], a[i]} | _t#0 == i + 1 :: 0 <= i && i < a.Length - 1 && a[i] + 1 == a[_t#0]
  decreases a
{
  result := false;
  for i: int := 0 to a.Length - 2
    invariant 0 <= i <= a.Length - 1
    invariant result <==> exists k: int, _t#0: int {:trigger a[_t#0], a[k]} | _t#0 == k + 1 :: 0 <= k && k < i && a[k] + 1 == a[_t#0]
  {
    if a[i] + 1 == a[i + 1] {
      result := true;
      break;
    }
  }
}
