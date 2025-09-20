// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug165.dfy

function f(a: T): bool

method Select(s1: seq<T>) returns (r: seq<T>)
  ensures forall e: T {:trigger multiset(r)[e]} {:trigger multiset(s1)[e]} {:trigger f(e)} :: f(e) ==> multiset(s1)[e] == multiset(r)[e]
  ensures forall e: T {:trigger multiset(r)[e]} {:trigger f(e)} :: !f(e) ==> 0 == multiset(r)[e]
  decreases s1

method Main(s1: seq<T>)
  decreases s1
{
  var r1, r2: seq<T>;
  r1 := Select(r1);
  r2 := Select(s1);
  assert multiset(r1) == multiset(r2);
}

type T(!new)
