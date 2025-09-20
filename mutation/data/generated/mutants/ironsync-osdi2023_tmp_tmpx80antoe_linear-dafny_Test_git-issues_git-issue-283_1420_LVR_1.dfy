// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_git-issues_git-issue-283.dfy

method Main()
{
  var t := new CL;
  m(t);
}

method m(t: Foo)
  decreases t
{
  t.FooMethod1(Result.Success(()));
  t.FooMethod2(Result<C>.Success(C1));
  t.FooMethod2q(Result<C>.Success(C1));
  t.FooMethod2r(Result<C>.Success(C1));
  t.FooMethod3(Result<C>.Success(C1));
  t.FooMethod4(Result<C>.Success(C1));
  t.FooMethod5(Result<string>.Success(""));
  print "Done\n";
}

datatype Result<T> = Success(value: T) | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo {
  method FooMethod1(r: Result<()>)
    ensures match r { case Success(()) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(()) =>
        x := 1;
      case {:split false} Failure(e) =>
        x := 2;
    }
    assert x > 0;
    expect x == 1, "expectation violation";
  }

  method FooMethod2(r: Result<C>)
    ensures match r { case Success(C1()) => true case Success(C2(x)) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(C1()) =>
        x := 1;
      case {:split false} Success(C2(_ /* _v0 */)) =>
        x := 2;
      case {:split false} Failure(e) =>
        x := 3;
    }
    assert x > 0;
    expect x == 1, "expectation violation";
  }

  method FooMethod2q(r: Result<C>)
    ensures match r { case Success(C1()) => true case Success(C2(x)) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(C1()) =>
        x := 1;
      case {:split false} Success(C2(x)) =>
        x := 1;
      case {:split false} Failure(e) =>
        x := 3;
    }
    assert x == 0 || x == 1 || x == 3;
    expect x == 0 || x == 1 || x == 3, "expectation violation";
  }

  method FooMethod2r(r: Result<C>)
    ensures match r { case Success(C1()) => true case Success(C2(x)) => true case Failure(e) => true }
    decreases r
  {
    var x: real := 0.0;
    match r {
      case {:split false} Success(C1()) =>
        x := 1.0;
      case {:split false} Success(C2(x)) =>
        x := 2;
      case {:split false} Failure(e) =>
        x := 3.0;
    }
    assert x == 0.0 || x == 1.0 || x == 3.0;
    expect x == 0.0 || x == 1.0 || x == 3.0, "expectation violation";
  }

  method FooMethod3(r: Result<C>)
    ensures match r { case Success(C1()) => true case Success(C2(x)) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(C1()) =>
        x := 1;
      case {:split false} Success(C2(_ /* _v1 */)) =>
        x := 2;
      case {:split false} Failure(e) =>
        x := 3;
    }
    assert x > 0;
    expect x == 1, "expectation violation";
  }

  method FooMethod4(r: Result<C>)
    ensures match r { case Success(C2) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(C2) =>
        x := 1;
      case {:split false} Failure(e) =>
        x := 2;
    }
    assert x > 0;
    expect x == 1, "expectation violation";
  }

  method FooMethod5(r: Result<string>)
    ensures match r { case Success(C1) => true case Failure(e) => true }
    decreases r
  {
    var x: int := 0;
    match r {
      case {:split false} Success(C1) =>
        x := 1;
      case {:split false} Failure(e) =>
        x := 2;
    }
    assert x > 0;
    expect x == 1, "expectation violation";
  }
}

class CL extends Foo { }
