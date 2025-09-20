// dafny-programs_tmp_tmpcwodh6qh_src_ticketsystem.dfy

type Process(==,!new)

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
    P <= cs.Keys &&
    P <= t.Keys &&
    serving <= ticket &&
    (forall p: Process {:trigger t[p]} {:trigger cs[p]} {:trigger p in P} :: 
      (p in P &&
      cs[p] != Thinking ==>
        serving <= t[p]) &&
      (p in P &&
      cs[p] != Thinking ==>
        t[p] < ticket)) &&
    (forall p: Process, q: Process {:trigger t[q], t[p]} {:trigger t[q], cs[p]} {:trigger t[q], p in P} {:trigger t[p], cs[q]} {:trigger t[p], q in P} {:trigger cs[q], cs[p]} {:trigger cs[q], p in P} {:trigger cs[p], q in P} {:trigger q in P, p in P} :: 
      p in P &&
      q in P &&
      p != q &&
      cs[p] != Thinking &&
      cs[q] != Thinking ==>
        t[p] != t[q]) &&
    forall p: Process {:trigger t[p]} {:trigger cs[p]} {:trigger p in P} :: 
      p in P &&
      cs[p] == Eating ==>
        t[p] == serving
  }

  constructor (processes: set<Process>)
    ensures Valid()
    decreases processes
  {
    P := processes;
    ticket, serving := 0, 0;
    cs := map p: Process {:trigger p in processes} | p in processes :: Thinking;
    t := map p: Process {:trigger p in processes} | p in processes :: 0;
  }

  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking
    modifies this
    ensures Valid()
  {
    t, ticket := t[p := ticket], ticket + 1;
    cs := cs[p := Hungry];
  }

  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry
    modifies this
    ensures Valid()
  {
    if t[p] == serving {
      cs := cs[p := Eating];
    }
  }

  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating
    modifies this
    ensures Valid()
  {
    assert t[p] == serving;
    serving := serving + -1;
    cs := cs[p := Thinking];
  }

  lemma MutualExclusion(p: Process, q: Process)
    requires Valid() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    ensures p == q
}
