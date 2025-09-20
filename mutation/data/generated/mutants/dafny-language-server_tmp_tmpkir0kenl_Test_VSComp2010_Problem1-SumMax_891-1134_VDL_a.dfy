// dafny-language-server_tmp_tmpkir0kenl_Test_VSComp2010_Problem1-SumMax.dfy

method M(N: int, a: array<int>)
    returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && forall k: int {:trigger a[k]} :: 0 <= k && k < N ==> 0 <= a[k]
  ensures sum <= N * max
  decreases N, a
{
  sum := 0;
  max := 0;
  var i := 0;
  while i < N
    invariant i <= N && sum <= i * max
    decreases N - i
  {
    if max < a[i] {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

method Main()
{
  print "N = ", "  sum = ", "  max = ", "\n";
}
