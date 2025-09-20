// Formal-Verification-Project_tmp_tmp9gmwsmyp_strings3.dfy

predicate isPrefixPred(pre: string, str: string)
  decreases pre, str
{
  |pre| <= |str| &&
  pre == str[..|pre|]
}

predicate isNotPrefixPred(pre: string, str: string)
  decreases pre, str
{
  |pre| > |str| || pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre: string, str: string)
  ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
  ensures !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str)
  decreases pre, str
{
}

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures !res <==> isNotPrefixPred(pre, str)
  ensures res <==> isPrefixPred(pre, str)
  decreases pre, str
{
  if |str| < |pre| {
    return false;
  } else if pre[..] == str[..|pre|] {
    return true;
  } else {
    return false;
  }
}

predicate isSubstringPred(sub: string, str: string)
  decreases sub, str
{
  exists i: int {:trigger str[i..]} :: 
    0 <= i <= |str| &&
    isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub: string, str: string)
  decreases sub, str
{
  forall i: int {:trigger str[i..]} :: 
    0 <= i <= |str| ==>
      isNotPrefixPred(sub, str[i..])
}

lemma SubstringNegationLemma(sub: string, str: string)
  ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
  ensures !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str)
  decreases sub, str
{
}

method isSubstring(sub: string, str: string) returns (res: bool)
  ensures res <==> isSubstringPred(sub, str)
  decreases sub, str
{
  var i := 0;
  res := false;
  while i != |str|
    invariant 0 <= i <= |str| + 1
    invariant forall j: int {:trigger str[j..]} :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    decreases |str| - i
  {
    var temp := isPrefix(sub, str[i..]);
    if temp == true {
      return true;
    }
    i := i + 1;
  }
  return false;
}

predicate haveCommonKSubstringPred(k: nat, str1: string, str2: string)
  decreases k, str1, str2
{
  exists i1: int, j1: int {:trigger str1[i1 .. j1]} :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k &&
    isSubstringPred(str1[i1 .. j1], str2)
}

predicate haveNotCommonKSubstringPred(k: nat, str1: string, str2: string)
  decreases k, str1, str2
{
  forall i1: int, j1: int {:trigger str1[i1 .. j1]} :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k ==>
      isNotSubstringPred(str1[i1 .. j1], str2)
}

lemma commonKSubstringLemma(k: nat, str1: string, str2: string)
  ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
  ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
  decreases k, str1, str2
{
}

method haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  ensures found <==> haveCommonKSubstringPred(k, str1, str2)
  decreases k, str1, str2
{
  if k > |str1| || k > |str2| {
    return false;
  }
  var i := 0;
  var temp := false;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant temp ==> 0 <= i <= |str1| - k && isSubstringPred(str1[i .. i + k], str2)
    invariant !temp ==> forall m: int, n: int {:trigger str1[m .. n]} :: 0 <= m < i && n == m + k ==> isNotSubstringPred(str1[m .. n], str2)
    decreases |str1| - k - i
  {
    temp := isSubstring(str1[i .. i + k], str2);
    if temp == true {
      return true;
    }
    i := i + 1;
  }
  return false;
}

lemma haveCommon0SubstringLemma(str1: string, str2: string)
  ensures haveCommonKSubstringPred(0, str1, str2)
  decreases str1, str2
{
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires |str1| <= |str2|
  ensures forall k: int {:trigger haveCommonKSubstringPred(k, str1, str2)} :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
  ensures haveCommonKSubstringPred(len, str1, str2)
  decreases str1, str2
{
  var temp := false;
  var i := |str1| + 1;
  len := i;
  while i > 0
    invariant 0 <= i <= |str1| + 1
    invariant temp ==> haveCommonKSubstringPred(i, str1, str2)
    invariant !temp ==> haveNotCommonKSubstringPred(i, str1, str2)
    invariant !temp ==> forall k: int {:trigger haveCommonKSubstringPred(k, str1, str2)} :: i <= k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    invariant temp ==> forall k: int {:trigger haveCommonKSubstringPred(k, str1, str2)} :: i < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    decreases i
  {
    i := i - 1;
    len := i;
    temp := haveCommonKSubstring(i, str1, str2);
    if temp == true {
      break;
    }
  }
  haveCommon0SubstringLemma(str1, str2);
  return len;
}
