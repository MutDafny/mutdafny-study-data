// CSC8204-Dafny_tmp_tmp11yhjb53_stack.dfy

function isEmpty(s: intStack): bool
  decreases s
{
  |s| == 0
}

function push(s: intStack, x: int): intStack
  decreases s, x
{
  s + [x]
}

function pop(s: intStack): intStack
  requires !isEmpty(s)
  decreases s
{
  s[..|s| - 1]
}

method testStack() returns (r: intStack)
{
  var s: intStack := [20, 30, 15, 40, 60, 0, 80];
  assert pop(push(s, 100)) == s;
  assert forall e: int {:trigger s[e]} :: 0 <= e < |s| ==> s[e] > 5;
  r := s;
}

method Main()
{
  var t := testStack();
  print "Stack tested\nStack is ", t, "\n";
}

type intStack = seq<int>
