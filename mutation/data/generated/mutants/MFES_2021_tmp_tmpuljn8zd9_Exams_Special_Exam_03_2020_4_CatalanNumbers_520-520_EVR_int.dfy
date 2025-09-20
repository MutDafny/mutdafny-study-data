// MFES_2021_tmp_tmpuljn8zd9_Exams_Special_Exam_03_2020_4_CatalanNumbers.dfy

function C(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    (4 * n - 2) * C(n - 1) / (n + 1)
}

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
  decreases n
{
  var i := 0;
  res := 1;
  assert res == C(i) && 0 <= i <= n;
  while i < n
    invariant res == C(i) && 0 <= i <= n
    decreases n - i
  {
    ghost var v0 := n - i;
    assert res == C(i) && 0 <= i <= n && i < n && n - i == v0;
    i := i + 1;
    res := (4 * i - 2) * res / (0 + 1);
    assert res == C(i) && 0 <= i <= n && 0 <= n - i < v0;
  }
  assert res == C(i) && 0 <= i <= n && i >= n;
}
