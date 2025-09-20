// dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_MatrixFun.dfy

method MirrorImage<T>(m: array2<T>)
  modifies m
  ensures forall i: int, j: int {:trigger m[i, j]} :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i, j] == old(m[i, m.Length1 - 1 - j])
  decreases m
{
  var a := 0;
  while a < m.Length0
    invariant a <= m.Length0
    invariant forall i: int, j: int {:trigger m[i, j]} :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==> m[i, j] == old(m[i, m.Length1 - 1 - j])
    invariant forall i: int, j: int {:trigger old(m[i, j])} {:trigger m[i, j]} :: a <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==> m[i, j] == old(m[i, j])
    decreases m.Length0 - a
  {
    var b := 0;
    while b < m.Length1 / 2
      invariant b <= m.Length1 / 2
      invariant forall i: int, j: int {:trigger m[i, j]} :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==> m[i, j] == old(m[i, m.Length1 - 1 - j])
      invariant (forall j: int {:trigger m[a, j]} :: 0 <= j && j < b ==> m[a, j] == old(m[a, m.Length1 - 1 - j])) && forall j: int, _t#0: int {:trigger m[a, _t#0], old(m[a, j])} {:trigger m[a, _t#0], m[a, j]} | _t#0 == m.Length1 - 1 - j :: 0 <= j && j < b ==> old(m[a, j]) == m[a, _t#0]
      invariant forall j: int {:trigger old(m[a, j])} {:trigger m[a, j]} :: b <= j && j < m.Length1 - b ==> m[a, j] == old(m[a, j])
      invariant forall i: int, j: int {:trigger old(m[i, j])} {:trigger m[i, j]} :: a + 1 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==> m[i, j] == old(m[i, j])
      decreases m.Length1 / 2 - b
    {
      m[a, m.Length1 - 1 - b], m[a, b] := m[a, b], m[a, m.Length1 - 1 - b];
      b := b + 1;
    }
    a := a + 1;
  }
}

method Flip<T>(m: array2<T>)
  requires m.Length0 == m.Length1
  modifies m
  ensures forall i: int, j: int {:trigger old(m[j, i])} {:trigger m[i, j]} :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i, j] == old(m[j, i])
  decreases m
{
  var N := m.Length0;
  var a := 0;
  var b := 1;
  while a != N
    invariant a < b <= N || (a == N && b == N + 1)
    invariant forall i: int, j: int {:trigger old(m[i, j])} {:trigger m[j, i]} {:trigger old(m[j, i])} {:trigger m[i, j]} :: 0 <= i <= j < N ==> if i < a || (i == a && j < b) then m[i, j] == old(m[j, i]) && m[j, i] == old(m[i, j]) else m[i, j] == old(m[i, j]) && m[j, i] == old(m[j, i])
    decreases N - a, N - b
  {
    if b < N {
      m[a, b], m[b, a] := m[b, a], m[a, b];
      b := b + 1;
    } else {
      a := a + 1;
      b := a + 1;
    }
  }
}

method Main()
{
  var B := new bool[2, 5];
  B[0, 0] := true;
  B[0, 1] := false;
  B[0, 2] := false;
  B[0, 3] := true;
  B[0, 4] := false;
  B[1, 0] := true;
  B[1, 1] := true;
  B[1, 2] := true;
  B[1, 3] := true;
  B[1, 4] := false;
  print "Before:\n";
  PrintMatrix(B);
  MirrorImage(B);
  print "Mirror image:\n";
  PrintMatrix(B);
  var A := new int[3, 3];
  A[0, 0] := 5;
  A[0, 1] := 7;
  A[0, 2] := 9;
  A[1, 0] := 6;
  A[1, 1] := 2;
  A[1, 2] := 3;
  A[2, 0] := 7;
  A[2, 1] := 1;
  A[2, 2] := 0;
  print "Before:\n";
  PrintMatrix(A);
  Flip(A);
  print "Flip:\n";
  PrintMatrix(A);
}

method PrintMatrix<T>(m: array2<T>)
  decreases m
{
  var i := 0;
  while i < m.Length0
    decreases m.Length0 - i
  {
    var j := 0;
    while j < m.Length1
      decreases m.Length1 - j
    {
      print m[i, j];
      j := j + 1;
      if j == 0 {
        print "\n";
      } else {
        print ", ";
      }
    }
    i := i + 1;
  }
}
