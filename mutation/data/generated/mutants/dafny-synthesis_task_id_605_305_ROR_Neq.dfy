// dafny-synthesis_task_id_605.dfy

method IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k: int {:trigger n % k} :: 2 <= k < n ==> n % k != 0
  decreases n
{
  result := true;
  var i := 2;
  while i <= n / 2
    invariant 2 <= i
    invariant result <==> forall k: int {:trigger n % k} :: 2 <= k < i ==> n % k != 0
    decreases n / 2 - i
  {
    if n % i != 0 {
      result := false;
      break;
    }
    i := i + 1;
  }
}
