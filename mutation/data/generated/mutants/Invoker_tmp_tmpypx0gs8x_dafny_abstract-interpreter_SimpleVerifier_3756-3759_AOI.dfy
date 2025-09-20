// Invoker_tmp_tmpypx0gs8x_dafny_abstract-interpreter_SimpleVerifier.dfy


module Ints {
  const U32_BOUND: nat := 4294967296

  newtype u32 = x: int
    | 0 <= x < 4294967296

  newtype i32 = x: int
    | -2147483648 <= x < 2147483648
}

module Lang {

  import opened Ints
  datatype Reg = R0 | R1 | R2 | R3

  datatype Expr = Const(n: u32) | Add(r1: Reg, r2: Reg) | Sub(r1: Reg, r2: Reg)

  datatype Stmt = Assign(r: Reg, e: Expr) | JmpZero(r: Reg, offset: i32)

  datatype Program = Program(stmts: seq<Stmt>)
}

module ConcreteEval {
  function update_state(s: State, r0: Reg, v: u32): State
    decreases r0, v
  {
    (r: Reg) => if r == r0 then v else s(r)
  }

  function expr_eval(env: State, e: Expr): Option<u32>
    decreases e
  {
    match e {
      case Const(n) =>
        Some(n)
      case Add(r1, r2) =>
        if env(r1) as int + env(r2) as int >= U32_BOUND then
          None
        else
          Some(env(r1) + env(r2))
      case Sub(r1, r2) =>
        if env(r1) as int - env(r2) as int < 0 then
          Some(0)
        else
          Some(env(r1) - env(r2))
    }
  }

  function stmt_step(env: State, s: Stmt): Option<(State, int)>
    decreases s
  {
    match s {
      case Assign(r, e) =>
        var e': Option<u32> := expr_eval(env, e);
        match e' {
          case Some(v) =>
            Some((update_state(env, r, v), 1))
          case None() =>
            None
        }
      case JmpZero(r, offset) =>
        Some((env, (if env(r) == 0 then offset else 1) as int))
    }
  }

  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
    decreases fuel
  {
    if fuel == 0 then
      NoFuel
    else if pc == |ss| then
      Ok(env)
    else
      match stmt_step(env, ss[pc]) { case None() => Error case Some((env', offset)) => if !(0 <= pc + offset <= |ss|) then Error else stmts_step(env', ss, pc + offset, fuel - 1) }
  }

  import opened Ints

  import opened Lang

  type State = Reg -> u32

  datatype Option<T> = Some(v: T) | None

  datatype ExecResult = Ok(env: State) | NoFuel | Error
}

module AbstractEval {
  function expr_eval(env: AbstractState, e: Expr): Val
    decreases env, e
  {
    match e {
      case Const(n) =>
        Interval(n as int, n as int)
      case Add(r1, r2) =>
        var v1: Val := env.rs(r1);
        var v2: Val := env.rs(r2);
        Interval(v1.lo + v2.lo, v1.hi + v2.hi)
      case Sub(r1, r2) =>
        var v1: Val := env.rs(r1);
        var v2: Val := env.rs(r2);
        Interval(0, if v1.hi - v2.lo >= 0 then -v1.hi - v2.lo else 0)
    }
  }

  function update_state(env: AbstractState, r0: Reg, v: Val): AbstractState
    decreases env, r0, v
  {
    AbstractState((r: Reg) => if r == r0 then v else env.rs(r))
  }

  function stmt_eval(env: AbstractState, s: Stmt): (AbstractState, set<int>)
    decreases env, s
  {
    match s {
      case Assign(r, e) =>
        var v: Val := expr_eval(env, e);
        (update_state(env, r, v), {1 as int})
      case JmpZero(r, offset) =>
        (env, {offset as int, 1})
    }
  }

  function has_valid_jump_targets(ss: seq<Stmt>, from: nat): bool
    requires from <= |ss|
    decreases |ss| - from
  {
    if from == |ss| then
      true
    else
      match ss[from] { case JmpZero(_ /* _v0 */, offset) => 0 <= from + offset as int <= |ss| case _ /* _v1 */ => true } && has_valid_jump_targets(ss, from + 1)
  }

  ghost predicate valid_jump_targets(ss: seq<Stmt>)
    decreases ss
  {
    forall i: int {:trigger ss[i]} | 0 <= i < |ss| :: 
      (ss[i].JmpZero? ==>
        0 <= i + ss[i].offset as int) &&
      (ss[i].JmpZero? ==>
        i + ss[i].offset as int <= |ss|)
  }

  lemma /*{:_inductionTrigger has_valid_jump_targets(ss, from)}*/ /*{:_induction ss, from}*/ has_valid_jump_targets_ok_helper(ss: seq<Stmt>, from: nat)
    requires from <= |ss|
    ensures has_valid_jump_targets(ss, from) <==> forall i: int {:trigger ss[i]} | from <= i < |ss| :: (ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int) && (ss[i].JmpZero? ==> i + ss[i].offset as int <= |ss|)
    decreases |ss| - from
  {
  }

  lemma /*{:_inductionTrigger valid_jump_targets(ss)}*/ /*{:_inductionTrigger has_valid_jump_targets(ss, 0)}*/ /*{:_induction ss}*/ has_valid_jump_targets_ok(ss: seq<Stmt>)
    ensures has_valid_jump_targets(ss, 0) <==> valid_jump_targets(ss)
    decreases ss
  {
    has_valid_jump_targets_ok_helper(ss, 0);
  }

  import opened Ints

  import opened Lang

  datatype Val = Interval(lo: int, hi: int)

  datatype AbstractState = AbstractState(rs: Reg -> Val)
}

module AbstractEvalProof {
  ghost predicate reg_included(c_v: u32, v: Val)
    decreases c_v, v
  {
    v.lo <= c_v as int <= v.hi
  }

  ghost predicate state_included(env: E.State, abs: AbstractState)
    decreases abs
  {
    forall r: Reg {:trigger abs.rs(r)} {:trigger env(r)} :: 
      reg_included(env(r), abs.rs(r))
  }

  lemma expr_eval_ok(env: E.State, abs: AbstractState, e: Expr)
    requires state_included(env, abs)
    requires E.expr_eval(env, e).Some?
    ensures reg_included(E.expr_eval(env, e).v, expr_eval(abs, e))
    decreases abs, e
  {
    match e {
      case {:split false} Add(_ /* _v2 */, _ /* _v3 */) =>
        {
          return;
        }
      case {:split false} Const(_ /* _v4 */) =>
        {
          return;
        }
      case {:split false} Sub(r1, r2) =>
        {
          assert reg_included(env(r1), abs.rs(r1));
          assert reg_included(env(r2), abs.rs(r2));
          assert env(r1) as int <= abs.rs(r1).hi;
          assert env(r2) as int >= abs.rs(r2).lo;
          if env(r1) <= env(r2) {
            assert E.expr_eval(env, e).v == 0;
            return;
          }
          assert E.expr_eval(env, e).v as int == env(r1) as int - env(r2) as int;
          return;
        }
    }
  }

  lemma stmt_eval_ok(env: E.State, abs: AbstractState, stmt: Stmt)
    requires state_included(env, abs)
    requires E.stmt_step(env, stmt).Some?
    ensures state_included(E.stmt_step(env, stmt).v.0, stmt_eval(abs, stmt).0)
    decreases abs, stmt
  {
  }

  import opened Ints

  import opened Lang

  import E = ConcreteEval

  import opened AbstractEval
}
