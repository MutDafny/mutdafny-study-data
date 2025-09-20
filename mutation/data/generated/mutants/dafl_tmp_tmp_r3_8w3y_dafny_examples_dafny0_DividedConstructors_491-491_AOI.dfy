// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_DividedConstructors.dfy

method Main()
{
  var m := new M0.MyClass.Init(20);
  print m.a, ", ", m.b, ", ", m.c, "\n";
  var r0 := new Regression.A.Make0();
  var r1 := new Regression.A.Make1();
  assert r0.b != r1.b;
  print r0.b, ", ", r1.b, "\n";
}

module M0 {
  class MyClass {
    var a: nat
    const b := 17
    var c: real

    constructor Init(x: nat)
      decreases x
    {
      this.a := x;
      c := 3.14;
      new;
      a := a + -b;
      assert c == 3.14;
      assert this.a == 17 + x;
    }

    constructor (z: real)
      ensures c <= 2.0 * z
      decreases z
    {
      a, c := 50, 2.0 * z;
      new;
    }

    constructor Make()
      ensures 10 <= a
    {
      new;
      a := a + b;
    }

    constructor Create()
      ensures 30 <= a
    {
      new;
      a := a + 2 * b;
    }
  }
}

module M1 refines M0 {
  class MyClass ... {
    const d := 'D'
    var e: char

    constructor Init(x: nat)
      decreases x
    {
      e := 'e';
      this.a := x;
      c := 3.14;
      new;
      e := 'x';
      a := a + -b;
      assert c == 3.14;
      assert this.a == 17 + x;
      assert e == 'x';
    }

    constructor (z: real)
      ensures c <= 2.0 * z
      decreases z
    {
      e := 'y';
      a, c := 50, 2.0 * z;
      new;
    }

    constructor Make()
      ensures 10 <= a
    {
      new;
      e := 'z';
      a := a + b;
    }

    constructor Create()
      ensures 30 <= a
    {
      e := 'w';
      new;
      a := a + 2 * b;
    }

    var a: nat
    const b := 17
    var c: real
  }
}

module TypeOfThis {
  class LinkedList<T(0)> {
    ghost var Repr: set<LinkedList<T>>
    ghost var Rapr: set<LinkedList?<T>>
    ghost var S: set<object>
    ghost var T: set<object?>

    constructor Init()
    {
      Repr := {this};
    }

    constructor Init'()
    {
      Rapr := {this};
    }

    constructor Create()
    {
      S := {this};
    }

    constructor Create'()
    {
      T := {this};
    }

    constructor Two()
    {
      new;
      var ll: LinkedList?<T> := this;
      var o: object? := this;
      if
      case true =>
        T := {o};
      case true =>
        S := {o};
      case true =>
        Repr := {ll};
      case true =>
        Rapr := {ll};
      case true =>
        S := {ll};
      case true =>
        T := {ll};
    }

    method Mutate()
      modifies this
    {
      Repr := {this};
      Rapr := {this};
      S := {this};
      T := {this};
    }
  }
}

module Regression {
  class A {
    var b: bool
    var y: int

    constructor Make0()
      ensures b == false
    {
      b := false;
    }

    constructor Make1()
      ensures b == true
    {
      b := true;
    }

    constructor Make2()
    {
      b := false;
      new;
      assert !b;
    }

    constructor Make3()
      ensures b == false && y == 65
    {
      b := false;
      y := 65;
      new;
      assert !b;
      assert y == 65;
    }

    constructor Make4(bb: bool, yy: int)
      ensures b == bb && y == yy
      decreases bb, yy
    {
      b, y := bb, yy;
    }
  }
}
