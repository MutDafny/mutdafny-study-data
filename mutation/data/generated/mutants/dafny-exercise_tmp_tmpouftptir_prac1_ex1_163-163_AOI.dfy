// dafny-exercise_tmp_tmpouftptir_prac1_ex1.dfy

predicate acheck(a: array<int>, n: int)
  requires n >= 1
  reads a
  decreases {a}, a, n
{
  a.Length % 2 == 0 &&
  forall i: int, _t#0: int {:trigger a[_t#0], a[i]} {:trigger a[_t#0], i % n} | _t#0 == -i :: 
    0 <= i &&
    i < a.Length ==>
      if i % n == 0 then a[i] == 0 else a[_t#0] != 0
}

method Main()
{
  var arr: array<int> := new int[] [0, 42, 0, 42];
  var res := acheck(arr, 2);
  assert res;
  arr := new int[] [];
  res := acheck(arr, 2);
  assert res;
  arr := new int[] [0, 4, 2, 0];
  assert arr[2] == 2;
  res := acheck(arr, 2);
  assert !res;
}
