// cs686_tmp_tmpdhuh5dza_classNotes_notes-9-8-21.dfy

method Q1()
{
  var a := new int[6];
  a[0], a[1], a[2], a[3], a[4], a[5] := 1, 0, 0, 0, 1, 1;
  var b := new int[3];
  b[0], b[1], b[2] := 1, 0, 1;
  var j, k := 1, 3;
  var p, r := 4, 5;
  assert forall i: int {:trigger a[i]} :: j <= i <= k ==> a[i] == 0;
  assert forall i: int {:trigger a[i]} :: if j <= i <= k then a[i] == 0 else true;
  assert forall i: int {:trigger a[i]} :: (0 <= i < a.Length && a[i] == 0 ==> j <= i) && (0 <= i < a.Length && a[i] == 0 ==> i <= k);
  assert a[0] == 1;
  assert !forall i: int {:trigger a[i]} :: (0 <= i < a.Length && a[i] == 1 ==> p <= i) && (0 <= i < a.Length && a[i] == 1 ==> i <= r);
  assert a[1] == 0 && a[2] == 0;
  assert exists i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length && a[i] == 0 && a[j] == 0;
  assert !exists i: int, j: int, k: int {:trigger b[k], b[j], b[i]} :: 0 <= i < j < k < b.Length && b[i] == 0 && b[j] == 0 && b[k] == k;
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
    x, y := testObject.Guess(0);
    assert x == true && y == 2;
  }
}
