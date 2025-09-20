// dafny-synthesis_task_id_3.dfy

method IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k: int {:trigger n % k} :: 2 <= k < n && n % k == 0
  decreases n
{
  result := false;
  var i := 2;
  while i <= n / 2
    invariant 2 <= i
    invariant result <==> exists k: int {:trigger n % k} :: 2 <= k < i && n % k == 0
    decreases n / 2 - i
  {
    result := true;
    break;
    i := i + 1;
  }
}
