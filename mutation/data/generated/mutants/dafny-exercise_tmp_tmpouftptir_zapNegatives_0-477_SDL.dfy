// dafny-exercise_tmp_tmpouftptir_zapNegatives.dfy

method ZapNegatives(a: array<int>)
  modifies a
  ensures forall i: int {:trigger a[i]} {:trigger old(a[i])} :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 else a[i] == old(a[i])
  ensures a.Length == old(a).Length
  decreases a
{
}

method Main()
{
  var arr: array<int> := new int[] [-1, 2, 3, -4];
  assert arr[0] == -1 && arr[1] == 2 && arr[2] == 3 && arr[3] == -4;
  ZapNegatives(arr);
  assert arr[0] == 0 && arr[1] == 2 && arr[2] == 3 && arr[3] == 0;
}
