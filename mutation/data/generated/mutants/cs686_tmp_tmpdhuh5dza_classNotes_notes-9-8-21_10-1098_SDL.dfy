// cs686_tmp_tmpdhuh5dza_classNotes_notes-9-8-21.dfy

method Q1()
{
}

class Secret {
  var secret: int
  var known: bool
  var count: int

  method Init(x: int)
    requires 1 <= x <= 10
    modifies `secret, `known, `count
    ensures secret == x
    ensures known == false
    ensures count == 0
    decreases x
  {
    known := false;
    count := 0;
    secret := x;
  }

  method Guess(g: int) returns (result: bool, guesses: int)
    requires known == false
    modifies `known, `count
    ensures if g == secret then result == true && known == true else result == false && known == false
    ensures count == old(count) + 1 && guesses == count
    decreases g
  {
    if g == secret {
      known := true;
      result := true;
    } else {
      result := false;
    }
    count := count + 1;
    guesses := count;
  }

  method Main()
  {
    var testObject: Secret := new Secret.Init(5);
    assert 1 <= testObject.secret <= 10;
    assert testObject.secret == 5;
    var x, y := testObject.Guess(0);
    assert x == false && y == 1;
    x, y := testObject.Guess(5);
    assert x == true && y == 2;
  }
}
