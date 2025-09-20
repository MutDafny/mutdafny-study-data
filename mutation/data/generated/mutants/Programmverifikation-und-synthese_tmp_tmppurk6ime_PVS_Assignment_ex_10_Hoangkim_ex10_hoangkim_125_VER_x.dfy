// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_10_Hoangkim_ex10_hoangkim.dfy

method square0(n: nat) returns (sqn: nat)
  ensures sqn == n * n
  decreases n
{
  sqn := 0;
  var i := 0;
  var x;
  while x < n
    invariant i <= n && sqn == i * i
    decreases n - x
  {
    x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
}

method square1(n: nat) returns (sqn: nat)
  ensures sqn == n * n
  decreases n
{
  sqn := 0;
  var i := 0;
  while i < n
    invariant i <= n && sqn == i * i
    decreases n - i
  {
    var x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
}

method q(x: nat, y: nat) returns (z: nat)
  requires y - x > 2
  ensures x < z * z < y
  decreases x, y

method strange()
  ensures 1 == 2
{
  var x := 4;
  var c: nat := q(x, 2 * x);
}

method test0()
{
  var x: int := *;
  assume x * x < 100;
  assert x <= 9;
}
