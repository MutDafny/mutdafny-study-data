// dafny-sandbox_tmp_tmp3tu2bu8a_Stlc.dfy

predicate value(t: tm)
  decreases t
{
  t.tabs?
}

function fv(t: tm): set<int>
  decreases t
{
  match t
  case tvar(id) =>
    {id}
  case tabs(x, T, body) =>
    fv(body) - {x}
  case tapp(f, arg) =>
    fv(f) + fv(arg)
}

function subst(x: int, s: tm, t: tm): tm
  decreases x, s, t
{
  match t
  case tvar(x') =>
    if x == x' then
      s
    else
      t
  case tabs(x', T, t1) =>
    tabs(x', T, if x == x' then t1 else subst(x, s, t1))
  case tapp(t1, t2) =>
    tapp(subst(x, s, t1), subst(x, s, t2))
}

function step(t: tm): option<tm>
  decreases t
{
  if t.tapp? && t.f.tabs? && value(t.arg) then
    Some(subst(t.f.x, t.arg, t.f.body))
  else if t.tapp? && step(t.f).Some? then
    Some(tapp(step(t.f).get, t.arg))
  else if t.tapp? && value(t.f) && step(t.arg).Some? then
    Some(tapp(t.f, step(t.arg).get))
  else
    None
}

predicate reduces_to(t: tm, t': tm, n: nat)
  decreases n
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n - 1))
}

lemma /*{:_inductionTrigger reduces_to(tm.tapp(tm.tabs(0, ty.TArrow(ty.TBase, ty.TBase), tm.tvar(0)), tm.tabs(0, ty.TBase, tm.tvar(0))), tm.tabs(0, ty.TBase, tm.tvar(0)), n)}*/ /*{:_induction n}*/ lemma_step_example1(n: nat)
  requires n > 0
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))), tabs(0, TBase, tvar(0)), n)
  decreases n
{
}

function find(c: map<int, ty>, x: int): option<ty>
  decreases c, x
{
  if x in c then
    Some(c[x])
  else
    None
}

function extend(x: int, T: ty, c: map<int, ty>): map<int, ty>
  decreases x, T, c
{
  c[x := T]
}

function has_type(c: map<int, ty>, t: tm): option<ty>
  decreases t
{
  match t
  case tvar(id) =>
    find(c, id)
  case tabs(x, T, body) =>
    var ty_body: option<ty> := has_type(extend(x, T, c), body);
    if ty_body.Some? then
      Some(TArrow(T, ty_body.get))
    else
      None
  case tapp(f, arg) =>
    var ty_f: option<ty> := has_type(c, f);
    var ty_arg: option<ty> := has_type(c, arg);
    if ty_f.Some? && ty_arg.Some? then
      if ty_f.get.TArrow? && ty_f.get.T1 == ty_arg.get then
        Some(ty_f.get.T2)
      else
        None
    else
      None
}

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase))
{
}

lemma example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) == Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)))
{
  ghost var c := extend(1, TArrow(TBase, TBase), extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tvar(0)) == Some(TBase);
  assert has_type(c, tvar(1)) == Some(TArrow(TBase, TBase));
  assert has_type(c, tapp(tvar(1), tapp(tvar(1), tvar(0)))) == Some(TBase);
}

lemma nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None
{
  ghost var c := extend(1, TBase, extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tapp(tvar(0), tvar(1))) == None;
}

lemma /*{:_inductionTrigger tm.tabs(0, S, tm.tapp(tm.tvar(0), tm.tvar(0)))}*/ /*{:_induction S}*/ nonexample_typing_3(S: ty, T: ty)
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T)
  decreases S, T
{
  ghost var c := extend(0, S, map[]);
  assert has_type(c, tapp(tvar(0), tvar(0))) == None;
}

lemma /*{:_inductionTrigger step(t)}*/ /*{:_inductionTrigger value(t)}*/ /*{:_inductionTrigger has_type(map[], t)}*/ /*{:_induction t}*/ theorem_progress(t: tm)
  requires has_type(map[], t).Some?
  ensures value(t) || step(t).Some?
  decreases t
{
}

lemma {:induction c, t} /*{:_inductionTrigger find(c, x), fv(t)}*/ /*{:_inductionTrigger has_type(c, t)}*/ /*{:_induction c, t}*/ lemma_free_in_context(c: map<int, ty>, x: int, t: tm)
  requires x in fv(t)
  requires has_type(c, t).Some?
  ensures find(c, x).Some?
  decreases t
{
}

predicate closed(t: tm)
  decreases t
{
  forall x: int {:trigger x in fv(t)} :: 
    x !in fv(t)
}

lemma /*{:_inductionTrigger closed(t)}*/ /*{:_inductionTrigger has_type(map[], t)}*/ /*{:_induction t}*/ corollary_typable_empty__closed(t: tm)
  requires has_type(map[], t).Some?
  ensures closed(t)
  decreases t
{
  forall x: int | true
    ensures x !in fv(t)
  {
    if x in fv(t) {
      lemma_free_in_context(map[], x, t);
      assert false;
    }
  }
}

lemma {:induction t} /*{:_inductionTrigger has_type(c', t)}*/ /*{:_inductionTrigger fv(t)}*/ /*{:_inductionTrigger has_type(c, t)}*/ /*{:_induction t}*/ lemma_context_invariance(c: map<int, ty>, c': map<int, ty>, t: tm)
  requires has_type(c, t).Some?
  requires forall x: int {:trigger find(c', x)} {:trigger find(c, x)} {:trigger x in fv(t)} :: x in fv(t) ==> find(c, x) == find(c', x)
  ensures has_type(c, t) == has_type(c', t)
  decreases t
{
  if t.tabs? {
    assert fv(t.body) == fv(t) || fv(t.body) == fv(t) + {t.x};
    lemma_context_invariance(extend(t.x, t.T, c), extend(t.x, t.T, c'), t.body);
  }
}

lemma /*{:_inductionTrigger has_type(c, subst(x, s, t))}*/ /*{:_inductionTrigger has_type(extend(x, has_type(map[], s).get, c), t)}*/ /*{:_induction c, x, s, t}*/ lemma_substitution_preserves_typing(c: map<int, ty>, x: int, s: tm, t: tm)
  requires has_type(map[], s).Some?
  requires has_type(extend(x, has_type(map[], s).get, c), t).Some?
  ensures has_type(c, subst(x, s, t)) == has_type(extend(x, has_type(map[], s).get, c), t)
  decreases t
{
  ghost var S := has_type(map[], s).get;
  ghost var cs := extend(x, S, c);
  ghost var T := has_type(cs, t).get;
  if t.tvar? {
    if t.id == x {
      assert T == S;
      corollary_typable_empty__closed(s);
      lemma_context_invariance(map[], c, s);
    }
  }
  if t.tabs? {
    if t.x == x {
      lemma_context_invariance(cs, c, t);
    } else {
      ghost var cx := extend(t.x, t.T, c);
      ghost var csx := extend(x, S, cx);
      ghost var cxs := extend(t.x, t.T, cs);
      lemma_context_invariance(cxs, csx, t.body);
      lemma_substitution_preserves_typing(cx, x, s, t.body);
    }
  }
}

lemma /*{:_inductionTrigger step(t)}*/ /*{:_inductionTrigger has_type(map[], t).Some?}*/ /*{:_induction t}*/ theorem_preservation(t: tm)
  requires has_type(map[], t).Some?
  requires step(t).Some?
  ensures has_type(map[], step(t).get) == has_type(map[], t)
  decreases t
{
  if t.tapp? && value(t.f) && value(t.arg) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.body);
  }
}

predicate normal_form(t: tm)
  decreases t
{
  false
}

predicate stuck(t: tm)
  decreases t
{
  normal_form(t) &&
  !value(t)
}

lemma /*{:_inductionTrigger reduces_to(t, t', n)}*/ /*{:_induction t, t', n}*/ corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t) == Some(T)
  requires reduces_to(t, t', n)
  ensures !stuck(t')
  decreases n
{
  theorem_progress(t);
  if t != t' {
    theorem_preservation(t);
    corollary_soundness(step(t).get, t', T, n - 1);
  }
}

datatype option<A> = None | Some(get: A)

datatype ty = TBase | TArrow(T1: ty, T2: ty)

datatype tm = tvar(id: int) | tapp(f: tm, arg: tm) | tabs(x: int, T: ty, body: tm)
