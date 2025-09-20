// DafnyProjects_tmp_tmp2acw_s4s_Graph.dfy

method testGraph()
{
  var G := new Graph<int>();
  assert G.E == {} && G.V == {};
  G.addVertex(1);
  G.addVertex(2);
  G.addVertex(3);
  G.addVertex(4);
  assert G.V == {1, 2, 3, 4};
  G.addEdge(1, 2);
  G.addEdge(1, 3);
  G.addEdge(2, 3);
  G.addEdge(0, 1);
  assert G.E == {(1, 2), (1, 3), (2, 3), (4, 1)};
  assert G.getAdj(1) == {2, 3};
  G.collapseVertices({1, 2, 3}, 3);
  assert G.V == {3, 4} && G.E == {(4, 3)};
}

class {:autocontracts} Graph<T(==)> {
  var V: set<T>
  var E: set<(T, T)>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this}
  {
    this in Repr &&
    null !in Repr &&
    forall e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in E} :: 
      (e in E ==>
        e.0 in V) &&
      (e in E ==>
        e.1 in V) &&
      (e in E ==>
        e.0 != e.1)
  }

  constructor ()
    ensures Valid()
    ensures fresh(Repr)
    ensures V == {} && E == {}
  {
    V := {};
    E := {};
    new;
    Repr := {this};
  }

  method addVertex(v: T)
    requires Valid()
    requires v !in V
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures E == old(E) && V == old(V) + {v}
  {
    V := V + {v};
  }

  method addEdge(u: T, v: T)
    requires Valid()
    requires u in V && v in V && (u, v) !in E && u != v
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures V == old(V) && E == old(E) + {(u, v)}
  {
    E := E + {(u, v)};
  }

  function getAdj(v: T): set<T>
    requires Valid()
    requires v in V
    reads Repr
    decreases Repr
  {
    set e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in E} | e in E && e.0 == v :: e.1
  }

  method removeVertex(v: T)
    requires Valid()
    requires v in V
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures V == old(V) - {v}
    ensures E == set e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in old(E)} | e in old(E) && e.0 != v && e.1 != v
  {
    V := V - {v};
    E := set e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in E} | e in E && e.0 != v && e.1 != v;
  }

  method collapseVertices(C: set<T>, v: T)
    requires Valid()
    requires v in C && C <= V
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures V == old(V) - C + {v}
    ensures E == set e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in old(E)} | e in old(E) && (e.0 !in C || e.1 !in C) :: (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
    decreases C
  {
    V := V - C + {v};
    E := set e: (T, T) {:trigger e.1} {:trigger e.0} {:trigger e in E} | e in E && (e.0 !in C || e.1 !in C) :: (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
  }

  ghost var Repr: set<object?>
}
