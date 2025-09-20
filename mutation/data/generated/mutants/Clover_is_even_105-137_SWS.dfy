// Clover_is_even.dfy

method ComputeIsEven(x: int) returns (is_even: bool)
  ensures (x % 2 == 0) == is_even
  decreases x
{
  if x % 2 == 0 {
    is_even := true;
  }
  is_even := false;
}
