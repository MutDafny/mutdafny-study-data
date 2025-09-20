// CS5232_Project_tmp_tmpai_cfrng_test.dfy

method Main()
{
  var i := new Gen(30);
  while true
    invariant i.Valid() && fresh(i._new)
    decreases 10 - |i.xs|
  {
    var m := i.MoveNext();
    if !m {
      break;
    }
    print i.x;
  }
}

iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
  decreases start
{
  var i := 0;
  while i < 10
    invariant |xs| == i
    decreases _yieldCount, 10 - i
  {
    x := start - i;
    yield;
    i := i + 1;
  }
}
