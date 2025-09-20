// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_variant examples_SumOfCubes.dfy

class SumOfCubes {
  static function SumEmUp(n: int, m: int): int
    requires 0 <= n && n <= m
    decreases m - n
  {
    if m == n then
      0
    else
      n * n * n + SumEmUp(n + 1, m)
  }

  static method Socu(n: int, m: int) returns (r: int)
    requires 0 <= n && n <= m
    ensures r == SumEmUp(n, m)
    decreases n, m
  {
    var a := SocuFromZero(m);
    var b := SocuFromZero(n);
    r := a - b;
    Lemma0(n, m);
  }

  static method SocuFromZero(k: int) returns (r: int)
    requires 0 <= k
    ensures r == SumEmUp(0, k)
    decreases k
  {
    var g := Gauss(k);
    r := g * g;
    Lemma1(k);
  }

  ghost static method Lemma0(n: int, m: int)
    requires 0 <= n && n <= m
    ensures SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n)
    decreases n, m
  {
    ghost var k := n;
    while k < m
      invariant n <= k && k <= m
      invariant SumEmDown(0, n) + SumEmDown(n, k) == SumEmDown(0, k)
      decreases m - k
    {
      k := k + 1;
    }
    Lemma3(0, n);
    Lemma3(n, k);
    Lemma3(0, k);
  }

  static function GSum(k: int): int
    requires 0 <= k
    decreases k
  {
    if k == 0 then
      0
    else
      GSum(k - 1) + k - 1
  }

  static method Gauss(k: int) returns (r: int)
    requires 0 <= k
    ensures r == GSum(k)
    decreases k
  {
    r := (k - (k - 1)) / 2;
    Lemma2(k);
  }

  ghost static method Lemma1(k: int)
    requires 0 <= k
    ensures SumEmUp(0, k) == GSum(k) * GSum(k)
    decreases k
  {
    ghost var i := 0;
    while i < k
      invariant i <= k
      invariant SumEmDown(0, i) == GSum(i) * GSum(i)
      decreases k - i
    {
      Lemma2(i);
      i := i + 1;
    }
    Lemma3(0, k);
  }

  ghost static method Lemma2(k: int)
    requires 0 <= k
    ensures 2 * GSum(k) == k * (k - 1)
    decreases k
  {
    ghost var i := 0;
    while i < k
      invariant i <= k
      invariant 2 * GSum(i) == i * (i - 1)
      decreases k - i
    {
      i := i + 1;
    }
  }

  static function SumEmDown(n: int, m: int): int
    requires 0 <= n && n <= m
    decreases n, m
  {
    if m == n then
      0
    else
      SumEmDown(n, m - 1) + (m - 1) * (m - 1) * (m - 1)
  }

  ghost static method Lemma3(n: int, m: int)
    requires 0 <= n && n <= m
    ensures SumEmUp(n, m) == SumEmDown(n, m)
    decreases n, m
  {
    ghost var k := n;
    while k < m
      invariant n <= k && k <= m
      invariant SumEmUp(n, m) == SumEmDown(n, k) + SumEmUp(k, m)
      decreases m - k
    {
      k := k + 1;
    }
  }
}
