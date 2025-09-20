// DafnyProjects_tmp_tmp2acw_s4s_findMax.dfy

method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k: int {:trigger a[k]} :: 0 <= k < a.Length && max == a[k]
  ensures forall k: int {:trigger a[k]} :: 0 <= k < a.Length ==> max >= a[k]
  decreases a
{
  max := a[0];
  for i: int := 1 to a.Length
    invariant exists k: int {:trigger a[k]} :: 0 <= k < i && max == a[k]
    invariant forall k: int {:trigger a[k]} :: 0 <= k < i ==> max >= a[k]
  {
    if a[i] > max {
      max := a[i];
    }
  }
}

method testFindMax()
{
  var a1 := new real[3] [1.0, 2.0, 3.0];
  var m1 := findMax(a1);
  assert m1 == a1[2] == 3.0;
  var a2 := new real[3] [3.0, 2.0, 1.0];
  var m2 := findMax(a2);
  assert m2 == a2[0] == 3.0;
  var a3 := new real[3] [2.0, 3.0, 1.0];
  var m3 := findMax(a3);
  assert m3 == a3[1] == 3.0;
  var a4 := new real[3] [1.0, 2.0, 2.0];
  var m4 := findMax(a4);
  assert m4 == a4[1] == 2.0;
  var a5 := new real[1] [1.0];
  var m5 := findMax(a5);
  assert m5 == a5[0] == 1.0;
  var a6 := new real[3] [1.0, 0.0, 1.0];
  var m6 := findMax(a6);
  assert m6 == a6[0] == 1.0;
}
