// dafny-synthesis_task_id_126.dfy

method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
  requires a > 0 && b > 0
  ensures sum >= 0
  ensures forall d: int {:trigger b % d} {:trigger a % d} :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
  decreases a, b
{
  sum := 0;
}
