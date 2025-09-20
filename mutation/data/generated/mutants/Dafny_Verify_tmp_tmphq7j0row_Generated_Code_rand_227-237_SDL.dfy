// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy

method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
  decreases xInit, y
{
  var x := xInit;
  z := x * y;
  while x > 0
    invariant x >= 0
    invariant z == x * y
    decreases x
  {
    z := z - y;
  }
}
