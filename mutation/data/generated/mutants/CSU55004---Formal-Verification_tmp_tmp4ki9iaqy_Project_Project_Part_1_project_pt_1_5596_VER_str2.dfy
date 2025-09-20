// CSU55004---Formal-Verification_tmp_tmp4ki9iaqy_Project_Project_Part_1_project_pt_1.dfy

method isPrefix(pre: string, str: string) returns (res: bool)
  requires 0 < |pre| <= |str|
  decreases pre, str
{
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    decreases |pre| - i
  {
    if str[i] != pre[i] {
      print str[i], " != ", pre[i], "\n";
      return false;
    } else {
      print str[i], " == ", pre[i], "\n";
      i := i + 1;
    }
  }
  return true;
}

method isSubstring(sub: string, str: string) returns (res: bool)
  requires 0 < |sub| <= |str|
  decreases sub, str
{
  var i := 0;
  var n := |str| - |sub|;
  while i < n + 1
    invariant 0 <= i <= n + 1
    decreases n - i
  {
    print "\n", sub, ", ", str[i .. |str|], "\n";
    var result := isPrefix(sub, str[i .. |str|]);
    if result == true {
      return true;
    } else {
      i := i + 1;
    }
  }
  return false;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  requires 0 < k <= |str1| && 0 < k <= |str2|
  decreases k, str1, str2
{
  var i := 0;
  var n := |str1| - k;
  while i < n
    decreases n - i
  {
    print "\n", str1[i .. i + k], ", ", str2, "\n";
    var result := isSubstring(str1[i .. i + k], str2);
    if result == true {
      return true;
    } else {
      i := i + 1;
    }
  }
  return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires 0 < |str1| && 0 < |str1|
  decreases str1, str2
{
  var result: bool;
  var i := |str1|;
  if |str2| < |str2| {
    i := |str2|;
  }
  while i > 0
    decreases i - 0
  {
    print str1, ", ", str2, " k = ", i, "\n";
    result := haveCommonKSubstring(i, str1, str2);
    if result == true {
      return i;
    } else {
      i := i - 1;
    }
  }
  return 0;
}

method Main()
{
  var prefix: string := "pre";
  var str_1: string := "prehistoric";
  var result: bool;
  var substring := "and";
  var str_2 := "operand";
  var string1 := "operation";
  var string2 := "irrational";
  var k: nat := 5;
  var x := maxCommonSubstringLength(string1, string2);
  print "Result: ", x, "\n";
}
