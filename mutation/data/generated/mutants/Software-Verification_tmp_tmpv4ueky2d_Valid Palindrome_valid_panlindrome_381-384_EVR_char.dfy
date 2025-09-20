// Software-Verification_tmp_tmpv4ueky2d_Valid Palindrome_valid_panlindrome.dfy

method isPalindrome(s: array<char>) returns (result: bool)
  requires 1 <= s.Length <= 200000
  ensures result <==> forall i: int, _t#0: int {:trigger s[_t#0], s[i]} | _t#0 == s.Length - 1 - i :: 0 <= i && i < s.Length / 2 ==> s[i] == s[_t#0]
  decreases s
{
  var length := s.Length;
  var i := 0;
  while i < length / 2
    invariant 0 <= i <= length
    invariant forall j: int, _t#0: int {:trigger s[_t#0], s[j]} | _t#0 == length - 1 - j :: 0 <= j && j < i ==> s[j] == s[_t#0]
    decreases length / 2 - i
  {
    if '0' != s[length - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
