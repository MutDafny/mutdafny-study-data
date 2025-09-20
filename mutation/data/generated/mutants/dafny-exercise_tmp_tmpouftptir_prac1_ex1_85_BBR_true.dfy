// dafny-exercise_tmp_tmpouftptir_prac1_ex1.dfy

predicate acheck(a: array<int>, n: int)
  requires n >= 1
  reads a
  decreases {a}, a, n
{
  true
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
