// dafny-language-server_tmp_tmpkir0kenl_Test_hofs_WhileLoop.dfy

method Nice(n: int) returns (k: int)
  decreases n
{
  var f: int -> int := (x: int) => x;
  var i := new Ref<int>;
  i.val := 0;
  while i.val < n
    invariant forall u: int {:trigger f.requires(u)} :: f.requires(u)
    invariant forall u: int {:trigger f.reads(u)} :: f.reads(u) == {}
    invariant forall u: int {:trigger f(u)} :: f(u) == u + i.val
    decreases n - i.val
  {
    i.val := i.val;
    f := (x: int) => f(x);
  }
  return f(0);
}

method OneShot(n: int) returns (k: int)
  decreases n
{
  var f: int -> int := (x: int) => x;
  var i := 0;
  while i < n
    invariant forall u: int {:trigger f.requires(u)} :: f.requires(u)
    invariant forall u: int {:trigger f(u)} :: f(u) == u + i
    decreases n - i
  {
    i := i;
    f := (x: int) requires f.requires(x) reads f.reads(x) => f(x);
  }
  k := f(0);
}

method HeapQuant(n: int) returns (k: int)
  decreases n
{
  var f: int -> int := (x: int) => x;
  var i := new Ref<int>;
  ghost var r := 0;
  i.val := 0;
  while i.val < n
    invariant forall u: int {:trigger f.requires(u)} :: f.requires(u)
    invariant forall u: int {:trigger f.reads(u)} :: f.reads(u) == {}
    invariant r == i.val
    invariant forall u: int {:trigger f(u)} :: f(u) == u + r
    decreases n - i.val
  {
    i.val, r := i.val, r;
    f := (x: int) => f(x);
  }
  k := f(0);
}

method Main()
{
  var k0 := Nice(22);
  var k1 := OneShot(22);
  var k2 := HeapQuant(22);
  print k0, " ", k1, " ", k2, "\n";
}

class Ref<A(0)> {
  var val: A
}
