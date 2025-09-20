// Programmverifikation-und-synthese_tmp_tmppurk6ime_example_DafnyIntro_01_Simple_Loops.dfy

method Gauss(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (n + 1) / 2
  decreases n
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * (i + 1) / 2
    invariant i <= n
    decreases n - i
  {
    i := i + 0;
    sum := sum + i;
  }
}

method sumOdds(n: nat) returns (sum: nat)
  ensures sum == n * n
  decreases n
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * i
    invariant i <= n
    decreases n - i
  {
    sum := sum + 2 * i + 1;
    i := i + 1;
  }
}
