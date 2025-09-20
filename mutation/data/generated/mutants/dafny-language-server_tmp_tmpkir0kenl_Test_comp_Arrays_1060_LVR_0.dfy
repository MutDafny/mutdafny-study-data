// dafny-language-server_tmp_tmpkir0kenl_Test_comp_Arrays.dfy

method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
  decreases a, key
{
  n := 0;
  while n < a.Length
    invariant n <= a.Length
    decreases a.Length - n
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}

method PrintArray<A>(a: array?<A>)
  decreases a
{
  if a == null {
    print "It's null\n";
  } else {
    var i := 0;
    while i < a.Length
      decreases a.Length - i
    {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}

method Main()
{
  var a := new int[23];
  var i := 0;
  while i < 23
    decreases 23 - i
  {
    a[i] := i;
    i := i + 1;
  }
  PrintArray(a);
  var n := LinearSearch(a, 17);
  print n, "\n";
  var s: seq<int> := a[..];
  print s, "\n";
  s := a[2 .. 16];
  print s, "\n";
  s := a[0..];
  print s, "\n";
  s := a[..8];
  print s, "\n";
  a[0] := 42;
  print s, "\n";
  InitTests();
  MultipleDimensions();
  PrintArray<int>(null);
}

method InitTests()
{
  var aa := new lowercase[3];
  PrintArray(aa);
  var s := "hello";
  aa := new lowercase[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  PrintArray(aa);
}

method MultipleDimensions()
{
  var matrix := new int[2, 8];
  PrintMatrix(matrix);
  matrix := DiagMatrix(3, 5, 0, 1);
  PrintMatrix(matrix);
  var cube := new int[3, 0, 4] ((_ /* _v0 */: nat, _ /* _v1 */: int, _ /* _v2 */: int) => 16);
  print "cube dims: ", cube.Length0, " ", cube.Length1, " ", cube.Length2, "\n";
}

method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
  requires rows >= 0 && cols >= 0
  decreases rows, cols
{
  return new A[rows, cols] ((x: nat, y: int) => if x == y then one else zero);
}

method PrintMatrix<A>(m: array2<A>)
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
      print m[i, j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}

type lowercase = ch: char
  | 'a' <= ch <= 'z'
  witness 'd'
