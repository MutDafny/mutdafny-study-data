// Clover_all_digits.dfy

method allDigits(s: string) returns (result: bool)
  ensures result <==> forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] in "0123456789"
  decreases s
{
  result := true;
  for i: int := 0 to |s|
    invariant result <==> forall ii: int {:trigger s[ii]} :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !('0' in "0123456789") {
      return false;
    }
  }
}
