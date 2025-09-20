// dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy

method Main()
{
  print "1 = ", ((x: int) => x)(1), "\n";
  print "3 = ", ((x: int) => (y: int) => x + y)(1)(2), "\n";
  print "3 = ", ((x: int, y: int) => y + x)(1, 2), "\n";
  print "0 = ", (() => 0)(), "\n";
  var y := 1;
  var f := (x: int) => x + y;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  y := 2;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  var z := new Ref<int>(1);
  f := (x: int) reads z => x + z.val;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  z.val := 2;
  print "4 = ", f(2), "\n";
  print "5 = ", f(3), "\n";
  f := (x: int) => x;
  y := 10;
  while !(y > 0)
    invariant forall x: int {:trigger f.requires(x)} :: f.requires(x)
    invariant forall x: int {:trigger f.reads(x)} :: f.reads(x) == {}
  {
    f := (x: int) => f(x + y);
    y := y - 1;
  }
  print "55 = ", f(0), "\n";
  print "0 = ", ((x: int) => var y: int := x; y)(0), "\n";
  print "1 = ", ((y: int) => (x: int) => var y: int := x; y)(0)(1), "\n";
}

class Ref<A> {
  var val: A

  constructor (a: A)
    ensures val == a
  {
    val := a;
  }
}
