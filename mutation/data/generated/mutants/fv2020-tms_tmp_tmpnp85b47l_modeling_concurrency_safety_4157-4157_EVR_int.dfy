// fv2020-tms_tmp_tmpnp85b47l_modeling_concurrency_safety.dfy

method Run(processes: set<Process>)
  requires processes != {}
  decreases *
{
  var ts := new TicketSystem(processes);
  var schedule := [];
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];
  while true
    invariant ts.Valid()
    decreases *
  {
    var p :| p in ts.P;
    match ts.cs[p] {
      case {:split false} Thinking() =>
        ts.Request(0);
      case {:split false} Hungry() =>
        ts.Enter(p);
      case {:split false} Eating() =>
        ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
}

method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n: nat {:trigger schedule(n)} :: schedule(n) in processes
  decreases *
{
  var ts := new TicketSystem(processes);
  var n := 0;
  while true
    invariant ts.Valid()
    decreases *
  {
    var p := schedule(n);
    match ts.cs[p] {
      case {:split false} Thinking() =>
        ts.Request(p);
      case {:split false} Hungry() =>
        ts.Enter(p);
      case {:split false} Eating() =>
        ts.Leave(p);
    }
    n := n + 1;
  }
}

type Process(==) = int

datatype CState = Thinking | Hungry | Eating

class TicketSystem {
  var ticket: int
  var serving: int
  const P: set<Process>
  var cs: map<Process, CState>
  var t: map<Process, int>

  predicate Valid()
    reads this
    decreases {this}
  {
    cs.Keys == t.Keys == P &&
    serving <= ticket &&
    (forall p: int {:trigger t[p]} {:trigger cs[p]} {:trigger p in P} :: 
      (p in P &&
      cs[p] != Thinking ==>
        serving <= t[p]) &&
      (p in P &&
      cs[p] != Thinking ==>
        t[p] < ticket)) &&
    (forall p: int, q: int {:trigger t[q], t[p]} {:trigger t[q], cs[p]} {:trigger t[q], p in P} {:trigger t[p], cs[q]} {:trigger t[p], q in P} {:trigger cs[q], cs[p]} {:trigger cs[q], p in P} {:trigger cs[p], q in P} {:trigger q in P, p in P} :: 
      p in P &&
      q in P &&
      p != q &&
      cs[p] != Thinking &&
      cs[q] != Thinking ==>
        t[p] != t[q]) &&
    forall p: int {:trigger t[p]} {:trigger cs[p]} {:trigger p in P} :: 
      p in P &&
      cs[p] == Eating ==>
        t[p] == serving
  }

  constructor (processes: set<Process>)
    ensures Valid()
    ensures P == processes
    decreases processes
  {
    P := processes;
    ticket, serving := 0, 0;
    cs := map p: int {:trigger p in processes} | p in processes :: Thinking;
    t := map p: int {:trigger p in processes} | p in processes :: 0;
  }

  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking
    modifies this
    ensures Valid()
    decreases p
  {
    t, ticket := t[p := ticket], ticket + 1;
    cs := cs[p := Hungry];
  }

  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry
    modifies this
    ensures Valid()
    decreases p
  {
    if t[p] == serving {
      cs := cs[p := Eating];
    }
  }

  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating
    modifies this
    ensures Valid()
    decreases p
  {
    serving := serving + 1;
    cs := cs[p := Thinking];
  }

  lemma MutualExclusion(p: Process, q: Process)
    requires Valid() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    ensures p == q
    decreases p, q
  {
  }
}
