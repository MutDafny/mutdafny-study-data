// DafnyProjects_tmp_tmp2acw_s4s_RawSort.dfy

ghost predicate sorted(a: array<T>)
  reads a
  decreases {a}, a
{
  forall i: int, j: int {:trigger a[j], a[i]} :: 
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}

ghost function inversions(a: array<T>): set<(nat, nat)>
  reads a
  decreases {a}, a
{
  set i: int, j: int {:trigger (i, j)} {:trigger a[j], a[i]} | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)
}

method rawsort(a: array<T>)
  modifies a
  ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
  decreases |inversions(a)|
{
  if i: int, j: int {:trigger a[j], a[i]} :| 0 <= i < j < a.Length && a[i] > a[j] {
    ghost var bef := inversions(a);
    a[i], a[j] := a[j], a[i];
    ghost var aft := inversions(a);
    ghost var aft2bef := map p: (int, int) {:trigger p.1} {:trigger p.0} {:trigger p in aft} | p in aft :: (if p.0 == i && p.1 > j then j else if p.0 == j then i else p.0, if p.1 == i then j else if p.1 == j && p.0 < i then i else p.1);
    mappingProp(aft, bef, (i, j), aft2bef);
    rawsort(a);
  }
}

lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  requires k in b
  requires forall x: T1 {:trigger m[x]} {:trigger x in m} {:trigger x in a} :: (x in a ==> x in m) && (x in a ==> m[x] in b - {k})
  requires forall x: T1, y: T1 {:trigger m[y], m[x]} {:trigger m[y], x in a} {:trigger m[x], y in a} {:trigger y in a, x in a} :: x in a && y in a && x != y ==> m[x] != m[y]
  ensures |a| < |b|
  decreases a, b, m
{
  if x: T1 {:trigger x in a} :| x in a {
    mappingProp(a - {x}, b - {m[x]}, k, m);
  }
}

method testRawsort()
{
  var a: array<T> := new T[] [3, 5, 1];
  assert a[..] == [3, 5, 1];
  rawsort(a);
  assert a[..] == [1, 3, 5];
}

type T = int
