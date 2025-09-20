// verified-using-dafny_tmp_tmp7jatpjyn_longestZero.dfy

function getSize(i: int, j: int): int
  decreases i, j
{
  j - i + 1
}

method longestZero(a: array<int>) returns (sz: int, pos: int)
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i: int {:trigger a[i]} :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i: int, j: int {:trigger getSize(i, j)} :: 0 <= i < j < a.Length && getSize(i, j) > sz ==> exists k: int {:trigger a[k]} :: i <= k <= j && a[k] != 0
  decreases a
{
  var b := new int[a.Length];
  if a[0] == 0 {
    b[0] := 1;
  } else {
    b[0] := 0;
  }
  var idx: int := 0;
  while idx < a.Length - 1
    invariant 0 <= idx <= a.Length - 1
    invariant forall i: int {:trigger b[i]} :: (0 <= i <= idx ==> 0 <= b[i]) && (0 <= i <= idx ==> b[i] <= a.Length)
    invariant forall i: int {:trigger b[i]} :: 0 <= i <= idx ==> -1 <= i - b[i]
    invariant forall i: int {:trigger b[i]} :: 0 <= i <= idx ==> forall j: int {:trigger a[j]} :: i - b[i] < j <= i ==> a[j] == 0
    invariant forall i: int {:trigger b[i]} :: 0 <= i <= idx ==> 0 <= i - b[i] ==> a[i - b[i]] != 0
    decreases a.Length - 1 - idx
  {
    if a[idx + 1] == 0 {
      b[idx + 1] := b[idx] + 1;
    } else {
      b[idx + 1] := 0;
    }
    idx := idx + 1;
  }
  idx := 1;
  sz := b[0];
  pos := 0;
  while idx < pos
    invariant 1 <= idx <= b.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant forall i: int {:trigger b[i]} :: 0 <= i < idx ==> b[i] <= sz
    invariant forall i: int {:trigger a[i]} :: pos <= i < pos + sz ==> a[i] == 0
    invariant forall i: int, j: int {:trigger getSize(i, j)} :: 0 <= i < j < idx && getSize(i, j) > sz ==> a[j - b[j]] != 0
    decreases pos - idx
  {
    if b[idx] > sz {
      sz := b[idx];
      pos := idx - b[idx] + 1;
    }
    idx := idx + 1;
  }
}

method Main()
{
  var a := new int[10];
  forall i: int | 0 <= i < a.Length {
    a[i] := 0;
  }
  a[3] := 1;
  var sz, pos := longestZero(a);
  print a[..], "\n";
  print a[pos .. sz + pos], "\n";
}
