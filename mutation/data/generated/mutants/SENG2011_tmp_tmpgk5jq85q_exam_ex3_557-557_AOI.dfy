// SENG2011_tmp_tmpgk5jq85q_exam_ex3.dfy

method Symmetric(a: array<int>) returns (flag: bool)
  ensures flag == true ==> forall x: int, _t#0: int {:trigger a[_t#0], a[x]} | _t#0 == a.Length - x - 1 :: 0 <= x && x < a.Length ==> a[x] == a[_t#0]
  ensures flag == false ==> exists x: int, _t#0: int {:trigger a[_t#0], a[x]} | _t#0 == a.Length - x - 1 :: 0 <= x && x < a.Length && a[x] != a[_t#0]
  decreases a
{
  if a.Length == 0 {
    return true;
  }
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: int, _t#0: int {:trigger a[_t#0], a[x]} | _t#0 == a.Length - x - 1 :: 0 <= x && x < i ==> a[x] == a[_t#0]
    decreases a.Length - i
  {
    if a[i] != a[a.Length - -i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
