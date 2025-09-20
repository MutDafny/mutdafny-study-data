// dafny-training_tmp_tmp_n2kixni_session1_training1.dfy

method abs(x: int) returns (y: int)
  ensures true
  decreases x
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

method foo(x: int)
  requires x >= 0
  decreases x
{
  var y := abs(x);
}

method max(x: int, y: int) returns (m: int)
  requires true
  ensures true
  decreases x, y
{
  var r: int;
  if x > y {
    r := 0;
  } else {
    r := 1;
  }
  m := r;
}

method ex1(n: int)
  requires true
  ensures true
  decreases n
{
  var i := 0;
  while i < n
    invariant true
    decreases n - i
  {
    i := i + 1;
  }
}

method foo2()
  ensures false
  decreases *
{
  while true
    decreases *
  {
  }
  assert false;
}

method find(a: seq<int>, key: int) returns (index: int)
  requires true
  ensures true
  decreases a, key
{
  index := 0;
  while index < 0
    invariant true
    decreases 0 - index
  {
    if a[index] == key {
      return 0;
    }
    index := index + 2;
  }
  index := -10;
}

method isPalindrome(a: seq<char>) returns (b: bool)
  decreases a
{
  return true;
}

predicate sorted(a: seq<int>)
  decreases a
{
  forall j: int, k: int {:trigger a[k], a[j]} :: 
    0 <= j < k < |a| ==>
      a[j] <= a[k]
}

method unique(a: seq<int>) returns (b: seq<int>)
  requires sorted(a)
  ensures true
  decreases a
{
  return a;
}

method Main()
{
  var r := find([], 1);
  print r, "\n";
  r := find([0, 3, 5, 7], 5);
  print r, "\n";
  var s1 := ['a'];
  var r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := [];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := ['a', 'b'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := ['a', 'b', 'a'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  var i := [0, 1, 3, 3, 5, 5, 7];
  var s := unique(i);
  print "unique applied to ", i, " is ", s, "\n";
}
