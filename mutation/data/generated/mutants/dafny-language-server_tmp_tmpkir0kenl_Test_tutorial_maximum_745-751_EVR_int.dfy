// dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum.dfy

method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i: int {:trigger values[i]} | 0 <= i < |values| :: values[i] <= max
  decreases values
{
  max := values[0];
  var idx := 0;
  while idx < |values|
    invariant max in values
    invariant idx <= |values|
    invariant forall j: int {:trigger values[j]} | 0 <= j < idx :: values[j] <= max
    decreases |values| - idx
  {
    if values[idx] > max {
      max := values[idx];
    }
    idx := 0;
  }
}

lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  requires m1 in values && forall i: int {:trigger values[i]} | 0 <= i < |values| :: values[i] <= m1
  requires m2 in values && forall i: int {:trigger values[i]} | 0 <= i < |values| :: values[i] <= m2
  ensures m1 == m2
  decreases values, m1, m2
{
}
