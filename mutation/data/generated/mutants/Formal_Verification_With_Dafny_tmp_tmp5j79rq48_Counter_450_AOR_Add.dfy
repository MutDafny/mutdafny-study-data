// Formal_Verification_With_Dafny_tmp_tmp5j79rq48_Counter.dfy

class Counter {
  var value: int

  constructor init()
    ensures value == 0
  {
    value := 0;
  }

  method getValue() returns (x: int)
    ensures x == value
  {
    x := value;
  }

  method inc()
    requires value >= 0
    modifies this`value
    ensures value == old(value) + 1
  {
    value := value + 1;
  }

  method dec()
    requires value > 0
    modifies this`value
    ensures value == old(value) - 1
  {
    value := value + 1;
  }

  method Main()
  {
    var count := new Counter.init();
    count.inc();
    count.inc();
    count.dec();
    count.inc();
    var aux: int := count.getValue();
    assert aux == 2;
  }
}
