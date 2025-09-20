// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_error_data_completion_06_n.dfy

method Main() returns (x: int, y: int)
  ensures x == y
{
  x := 0;
  y := 0;
  var w := 1;
  var z := 0;
  var turn := 0;
  while x != y
    invariant x == y ==> !(0 <= -z * 2 / 2 && 1 <= -(w - 1) * 2 / 2)
    invariant !((x != y && x - y <= -1) || (x - y >= 1 && -z * 2 / 2 <= 0 && (w - 1) * 2 / 2 <= 1))
    invariant !(w * 2 / 2 <= 0 && ((x != y && (x - y <= -1 || x - y >= 1)) || 1 <= z * 2 / 2))
    decreases if x <= y then y - x else x - y
  {
    if turn == 0 {
      turn := 1;
    }
    if turn == 1 {
      if w % 2 == 1 {
        x := x + 1;
      }
      turn := 1;
    } else {
      if turn == 2 {
        z := z + y;
        w := z + 1;
        turn := 0;
      }
    }
  }
}
