// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_selection_sort.dfy

predicate sorted(a: array<int>)
  requires a != null
  reads a
  decreases {a}, a
{
  sorted'(a, a.Length)
}

predicate sorted'(a: array<int>, i: int)
  requires a != null
  requires 0 <= i <= a.Length
  reads a
  decreases {a}, a, i
{
  forall k: int, _t#0: int {:trigger a[k], a[_t#0]} | _t#0 == k - 1 :: 
    0 < k &&
    k < i ==>
      a[_t#0] <= a[k]
}

method SelectionSort(a: array<int>)
  modifies a
  ensures sorted(a)
  decreases a
{
}
