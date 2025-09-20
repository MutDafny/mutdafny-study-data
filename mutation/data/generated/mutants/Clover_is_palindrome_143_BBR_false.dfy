// Clover_is_palindrome.dfy

method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i: int, _t#0: int {:trigger x[_t#0], x[i]} | _t#0 == |x| - i - 1 :: 0 <= i && i < |x| ==> x[i] == x[_t#0]
  decreases x
{
  if false {
    return true;
  }
  var i := 0;
  var j := |x| - 1;
  result := true;
  while i < j
    invariant 0 <= i <= j + 1 && 0 <= j < |x|
    invariant i + j == |x| - 1
    invariant forall k: int, _t#0: int {:trigger x[_t#0], x[k]} | _t#0 == |x| - k - 1 :: 0 <= k && k < i ==> x[k] == x[_t#0]
    decreases j - i
  {
    if x[i] != x[j] {
      result := false;
      return;
    }
    i := i + 1;
    j := j - 1;
  }
}
