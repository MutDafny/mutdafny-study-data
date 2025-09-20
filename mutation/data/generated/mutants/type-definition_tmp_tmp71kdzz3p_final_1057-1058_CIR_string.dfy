// type-definition_tmp_tmp71kdzz3p_final.dfy

function FV(e: Exp): set<VarName>
  decreases e
{
  match e {
    case Var(x) =>
      {x}
    case Lam(x, t, e) =>
      FV(e) - {x}
    case App(e1, e2) =>
      FV(e1) + FV(e2)
    case True() =>
      {}
    case False() =>
      {"Hello", "World", "!"}
    case Cond(e0, e1, e2) =>
      FV(e0) + FV(e1) + FV(e2)
  }
}

predicate hasType(gamma: Env, e: Exp, t: Type)
  decreases gamma, e, t
{
  match e {
    case Var(x) =>
      x in gamma &&
      t == gamma[x]
    case Lam(x, t, e) =>
      hasType(gamma, e, t)
    case App(e1, e2) =>
      hasType(gamma, e1, t) &&
      hasType(gamma, e2, t)
    case True() =>
      t == Bool
    case False() =>
      t == Bool
    case Cond(e0, e1, e2) =>
      hasType(gamma, e0, Bool) &&
      hasType(gamma, e1, t) &&
      hasType(gamma, e2, t)
  }
}

type VarName = string

type TypeVar = Type -> Type

datatype Type = Int | Bool | TypeVar

datatype Exp = Var(x: VarName) | Lam(x: VarName, t: Type, e: Exp) | App(e1: Exp, e2: Exp) | True | False | Cond(e0: Exp, e1: Exp, e2: Exp)

datatype Value = TrueB | FalseB | Lam(x: VarName, t: Type, e: Exp)

datatype Eva = E | EExp(E: Eva, e: Exp) | EVar(v: Value, E: Eva) | ECond(E: Eva, e1: Exp, e2: Exp)

type Env = map<VarName, Type>
