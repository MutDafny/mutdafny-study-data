// stunning-palm-tree_tmp_tmpr84c2iwh_ch5.dfy

function More(x: int): int
  decreases x
{
  if x <= 0 then
    1
  else
    More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
  decreases x
{
  if x <= 0 {
  } else {
    Increasing(x - 2);
  }
}

method ExampleLemmaUse(a: int)
  decreases a
{
  var b := More(a);
  Increasing(a);
  var c := More(b);
  Increasing(b);
  assert 2 <= c - a;
}

method ExampleLemmaUse50(a: int)
  decreases a
{
  var b := More(a);
  Increasing(a);
  var c := More(b);
  if a < 1000 {
    Increasing(b);
    assert 2 <= c - a;
  }
  assert a < 200 ==> 2 <= c - a;
}

method ExampleLemmaUse51(a: int)
  decreases a
{
  Increasing(a);
  var b := More(a);
  Increasing(b);
  b := More(b);
  if a < 1000 {
    assert 2 <= b - a;
  }
  assert a < 200 ==> 2 <= b - a;
}

function Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
  decreases m, n
{
  if n == 0 {
    calc {
      Ack(m, n);
    ==
      Ack(m - 1, 1);
    ==
      Ack(0, 1);
    ==
      1 + 1;
    ==
      2;
    ==
      n + 2;
    }
  } else {
    calc {
      Ack(m, n);
    ==
      Ack(m - 1, Ack(m, n - 1));
    ==
      Ack(0, Ack(1, n - 1));
    ==
      {
        Ack1n(1, n - 1);
      }
      Ack(0, n - 1 + 2);
    ==
      Ack(0, n + 1);
    ==
      n + 1 + 1;
    ==
      n + 2;
    }
  }
}

function Reduce(m: nat, x: int): int
  decreases m, x
{
  if m == 0 then
    x
  else
    Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
  decreases m, x
{
  if m == 0 {
    assert Reduce(0, x) == x;
  } else {
    calc {
      Reduce(m, x);
    ==
      Reduce(m / 2, x + 1) - m;
    <=
      {
        ReduceUpperBound(m / 2, x + 1);
      }
      Reduce(m / 2, x + 1) - m + x + 1 - Reduce(m / 2, x + 1);
    ==
      x - m + 1;
    <=
      {
        assert m >= 1;
      }
      x;
    }
  }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
  decreases m, x
{
  if m == 0 {
    assert x - 2 * 0 <= x == Reduce(0, x);
  } else {
    calc {
      Reduce(m, x);
    ==
      Reduce(m / 2, x + 1) - m;
    >=
      {
        ReduceLowerBound(m / 2, x + 1);
        assert x + 1 - m <= Reduce(m / 2, x + 1);
      }
      x + 1 - 2 * m;
    >
      x - 2 * m;
    }
  }
}

function Eval(e: Expr, env: map<string, nat>): nat
  decreases e, env
{
  match e {
    case Const(c) =>
      c
    case Var(s) =>
      if s in env then
        env[s]
      else
        0
    case Node(op, args) =>
      EvalList(op, args, env)
  }
}

function Unit(op: Op): nat
  decreases op
{
  match op
  case Add() =>
    0
  case Mul() =>
    1
}

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
  decreases args, op, env
{
  match args {
    case Nil() =>
      Unit(op)
    case Cons(e, tail) =>
      var v0: nat, v1: nat := Eval(e, env), EvalList(op, tail, env);
      match op
      case Add() =>
        v0 + v1
      case Mul() =>
        v0 * v1
  }
}

function Substitute(e: Expr, n: string, c: nat): Expr
  decreases e, n, c
{
  match e
  case Const(_ /* _v2 */) =>
    e
  case Var(s) =>
    if s == n then
      Const(c)
    else
      e
  case Node(op, args) =>
    Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
  decreases es, n, c
{
  match es
  case Nil() =>
    Nil
  case Cons(head, tail) =>
    Cons(Substitute(head, n, c), SubstituteList(tail, n, c))
}

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
  decreases e, n, c, env
{
  match e
  case {:split false} Const(_ /* _v3 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
      calc {
        Eval(Substitute(e, n, c), env);
        Eval(if s == n then Const(c) else e, env);
        if s == n then Eval(Const(c), env) else Eval(e, env);
        if s == n then c else Eval(e, env);
        if s == n then c else Eval(e, env[n := c]);
        if s == n then Eval(e, env[n := c]) else Eval(e, env[n := c]);
        Eval(e, env[n := c]);
      }
    }
  case {:split false} Node(op, args) =>
    {
      EvalSubstituteListCorrect(op, args, n, c, env);
    }
}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
  decreases args, op, n, c, env
{
  match args
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      calc {
        EvalList(op, SubstituteList(args, n, c), env);
      ==
        EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
      ==
        EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
      ==
        match op case Add() => Eval(Substitute(head, n, c), env) + EvalList(op, SubstituteList(tail, n, c), env) case Mul() => Eval(Substitute(head, n, c), env) * EvalList(op, SubstituteList(tail, n, c), env);
      ==
        {
          EvalSubstituteCorrect(head, n, c, env);
        }
        match op case Add() => Eval(head, env[n := c]) + EvalList(op, SubstituteList(tail, n, c), env) case Mul() => Eval(head, env[n := c]) * EvalList(op, SubstituteList(tail, n, c), env);
      ==
        {
          EvalSubstituteListCorrect(op, tail, n, c, env);
        }
        match op case Add() => Eval(head, env[n := c]) + EvalList(op, tail, env[n := c]) case Mul() => Eval(head, env[n := c]) * EvalList(op, tail, env[n := c]);
      ==
        EvalList(op, args, env[n := c]);
      }
    }
}

lemma /*{:_inductionTrigger Substitute(e, n, env[n])}*/ /*{:_induction e, n, env}*/ EvalEnv(e: Expr, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
  decreases e, n, env
{
  match e
  case {:split false} Const(_ /* _v4 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      match args
      case {:split false} Nil() =>
        {
        }
      case {:split false} Cons(head, tail) =>
        {
          EvalEnv(head, n, env);
          EvalEnvList(op, tail, n, env);
        }
    }
}

lemma /*{:_inductionTrigger EvalList(op, SubstituteList(es, n, env[n]), env)}*/ /*{:_induction op, es, n, env}*/ EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
  decreases es, op, n, env
{
  match es
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      EvalEnv(head, n, env);
      EvalEnvList(op, tail, n, env);
    }
}

lemma /*{:_inductionTrigger Substitute(e, n, 0), env.Keys}*/ /*{:_induction e, n, env}*/ EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
  decreases e, n, env
{
  match e
  case {:split false} Const(_ /* _v5 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      calc {
        Eval(Substitute(e, n, 0), env);
        EvalList(op, SubstituteList(args, n, 0), env);
      ==
        {
          EvalEnvDefaultList(op, args, n, env);
        }
        EvalList(op, args, env);
        Eval(e, env);
      }
    }
}

lemma /*{:_inductionTrigger EvalList(op, SubstituteList(args, n, 0), env)}*/ /*{:_induction op, args, n, env}*/ EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
  decreases args, op, n, env
{
  match args
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      EvalEnvDefault(head, n, env);
      EvalEnvDefaultList(op, tail, n, env);
    }
}

lemma /*{:_inductionTrigger Substitute(Substitute(e, n, c), n, c)}*/ /*{:_induction e, n, c}*/ SubstituteIdempotent(e: Expr, n: string, c: nat)
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
  decreases e, n, c
{
  match e
  case {:split false} Const(_ /* _v6 */) =>
    {
    }
  case {:split false} Var(_ /* _v7 */) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      SubstituteListIdempotent(args, n, c);
    }
}

lemma /*{:_inductionTrigger SubstituteList(SubstituteList(args, n, c), n, c)}*/ /*{:_induction args, n, c}*/ SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
  decreases args, n, c
{
  match args
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      SubstituteIdempotent(head, n, c);
      SubstituteListIdempotent(tail, n, c);
    }
}

function Optimize(e: Expr): Expr
  decreases e
{
  if e.Node? then
    var args: List<Expr> := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e
}

lemma /*{:_inductionTrigger Eval(Optimize(e), env)}*/ /*{:_induction e, env}*/ OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env)
  decreases e, env
{
  if e.Node? {
    OptimizeAndFilterCorrect(e.args, e.op, env);
    ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env);
  }
}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
  decreases args, u
{
  match args
  case Nil() =>
    Nil
  case Cons(head, tail) =>
    var hd: Expr, tl: List<Expr> := Optimize(head), OptimizeAndFilter(tail, u);
    if hd == Const(u) then
      tl
    else
      Cons(hd, tl)
}

lemma /*{:_inductionTrigger Eval(Expr.Node(op, OptimizeAndFilter(args, Unit(op))), env)}*/ /*{:_induction args, op, env}*/ OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env) == Eval(Node(op, args), env)
  decreases args, op, env
{
  match args
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      OptimizeCorrect(head, env);
      OptimizeAndFilterCorrect(tail, op, env);
    }
}

lemma /*{:_inductionTrigger List<Expr>.Cons(head, tail), Unit(op), Eval(head, env)}*/ /*{:_induction head, tail, op, env}*/ EvalListUnitHead(head: Expr, tail: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(head, env) == Unit(op) ==> EvalList(op, Cons(head, tail), env) == EvalList(op, tail, env)
  decreases head, tail, op, env
{
  ghost var ehead, etail := Eval(head, env), EvalList(op, tail, env);
  if ehead == Unit(op) {
    match op
    case {:split false} Add() =>
      {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==
          ehead + etail;
        ==
          etail;
        }
      }
    case {:split false} Mul() =>
      {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==
          ehead * etail;
        ==
          etail;
        }
      }
  }
}

function Shorten(op: Op, args: List<Expr>): Expr
  decreases op, args
{
  match args
  case Nil() =>
    Const(Unit(op))
  case Cons(head, Nil()) =>
    head
  case _ /* _v8 */ =>
    Node(op, args)
}

lemma /*{:_inductionTrigger Eval(Expr.Node(op, args), env)}*/ /*{:_inductionTrigger Eval(Shorten(op, args), env)}*/ /*{:_induction args, op, env}*/ ShortenCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
  decreases args, op, env
{
  match args
  case {:split false} Nil() =>
    {
    }
  case {:split false} Cons(head, Nil()) =>
    {
      calc {
        Eval(Node(op, args), env);
        EvalList(op, Cons(head, Nil), env);
        Eval(head, env);
      }
    }
  case {:split false} _ /* _v9 */ =>
    {
    }
}

datatype Expr = Const(nat) | Var(string) | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
