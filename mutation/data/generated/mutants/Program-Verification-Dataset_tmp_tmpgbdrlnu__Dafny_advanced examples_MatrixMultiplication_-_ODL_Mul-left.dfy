// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_MatrixMultiplication.dfy

function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
  requires m1 != null && m2 != null && m1.Length1 == m2.Length0
  requires row < m1.Length0 && column < m2.Length1
  reads m1, m2
  decreases {m1, m2}, m1, m2, row, column
{
  RowColumnProductFrom(m1, m2, row, column, 0)
}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
  requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
  requires row < m1.Length0 && column < m2.Length1
  reads m1, m2
  decreases m1.Length1 - k
{
  if k == m1.Length1 then
    0
  else
    m1[row, k] * m2[k, column] + RowColumnProductFrom(m1, m2, row, column, k + 1)
}

method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
  requires m1 != null && m2 != null
  requires m1.Length1 == m2.Length0
  ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
  ensures forall i: int, j: int {:trigger RowColumnProduct(m1, m2, i, j)} {:trigger m3[i, j]} | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 :: m3[i, j] == RowColumnProduct(m1, m2, i, j)
  decreases m1, m2
{
  m3 := new int[m1.Length0, m2.Length1];
  var i := 0;
  while i < m1.Length0
    invariant 0 <= i <= m1.Length0
    invariant forall i': int, j': int {:trigger RowColumnProduct(m1, m2, i', j')} {:trigger m3[i', j']} | 0 <= i' < i && 0 <= j' < m2.Length1 :: m3[i', j'] == RowColumnProduct(m1, m2, i', j')
    decreases m1.Length0 - i
  {
    var j := 0;
    while j < m2.Length1
      invariant 0 <= j <= m2.Length1
      invariant forall i': int, j': int {:trigger RowColumnProduct(m1, m2, i', j')} {:trigger m3[i', j']} | 0 <= i' < i && 0 <= j' < m2.Length1 :: m3[i', j'] == RowColumnProduct(m1, m2, i', j')
      invariant forall j': int {:trigger RowColumnProduct(m1, m2, i, j')} {:trigger m3[i, j']} | 0 <= j' < j :: m3[i, j'] == RowColumnProduct(m1, m2, i, j')
      decreases m2.Length1 - j
    {
      var k := 0;
      m3[i, j] := 0;
      while k < m1.Length1
        invariant 0 <= k <= m1.Length1
        invariant forall i': int, j': int {:trigger RowColumnProduct(m1, m2, i', j')} {:trigger m3[i', j']} | 0 <= i' < i && 0 <= j' < m2.Length1 :: m3[i', j'] == RowColumnProduct(m1, m2, i', j')
        invariant forall j': int {:trigger RowColumnProduct(m1, m2, i, j')} {:trigger m3[i, j']} | 0 <= j' < j :: m3[i, j'] == RowColumnProduct(m1, m2, i, j')
        invariant RowColumnProduct(m1, m2, i, j) == m3[i, j] + RowColumnProductFrom(m1, m2, i, j, k)
        decreases m1.Length1 - k
      {
        m3[i, j] := m3[i, j] + m2[k, j];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
