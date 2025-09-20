// dafny-learn_tmp_tmpn94ir40q_R01_functions.dfy

function abs(x: int): int
  decreases x
{
  if x < 0 then
    -x
  else
    x
}

method Testing_abs()
{
  var v := abs(3);
  assert v == 3;
}

function max(a: int, b: int): int
  decreases a, b
{
  if a > b then
    a
  else
    b
}

method Testing_max()
{
  assert max(3, 4) == 4;
  assert max(-1, -4) == -1;
}

method Abs(x: int) returns (y: int)
  ensures abs(x) == y
  decreases x
{
  if -x < 0 {
    return -x;
  } else {
    return x;
  }
}

ghost function Double(val: int): int
  decreases val
{
  2 * val
}

method TestDouble(val: int) returns (val2: int)
  ensures val2 == Double(val)
  decreases val
{
  val2 := 2 * val;
}
