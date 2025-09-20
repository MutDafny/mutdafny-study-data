// dafny-synthesis_task_id_126.dfy

method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
  requires a > 0 && b > 0
  ensures sum >= 0
  ensures forall d: int {:trigger b % d} {:trigger a % d} :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
  decreases a, b
{
  sum := 0;
  var i := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && 1 <= i <= b + 1
    invariant sum >= 0
    invariant forall d: int {:trigger b % d} {:trigger a % d} :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
    decreases a - i, if i <= a then b - i else 0 - 1
  {
    if a - i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}
