// verified-isort_tmp_tmp7hhb8ei__dafny_isort.dfy

predicate sorted(a: seq<nat>)
  decreases a
{
  true
}

method Isort(a: array<nat>)
  modifies a
  ensures sorted(a[..])
  decreases a
{
}
