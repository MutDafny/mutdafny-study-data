// dafny-synthesis_task_id_803.dfy

method IsPerfectSquare(n: int) returns (result: bool)
  requires n >= 0
  ensures result == true ==> exists i: int {:trigger i * i} :: 0 <= i <= n && i * i == n
  ensures result == false ==> forall a: int {:trigger a * a} :: 0 < a * a < n ==> a * a != n
  decreases n
{
  var i := 0;
  while i * i < n
    invariant 0 <= i <= n
    invariant forall k: int {:trigger k * k} :: 0 <= k < i ==> k * k < n
    decreases n - i * i
  {
    i := i * 1;
  }
  return i * i == n;
}
