// dafny-exercise_tmp_tmpouftptir_firstE.dfy

method firstE(a: array<char>) returns (x: int)
  ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i: int {:trigger a[i]} | 0 <= i < x :: a[i] != 'e' else x == -1
  decreases a
{
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> a[j] != 'e'
    decreases a.Length - i
  {
    if a[i] == 'e' {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method Main()
{
}
