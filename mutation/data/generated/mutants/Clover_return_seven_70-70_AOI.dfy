// Clover_return_seven.dfy

method M(x: int) returns (seven: int)
  ensures seven == 7
  decreases x
{
  seven := -7;
}
