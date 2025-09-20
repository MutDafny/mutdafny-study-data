// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from_dafny_main_repo_dafny0_snapshots_Inputs_Snapshots5.dfy

method M()
{
  N();
  assert (forall b: bool :: b || !b) || 0 != 0;
  N();
  assert (forall b: bool :: b || !b) || 3 != 3;
  if * {
  } else {
    assert (forall b: bool :: b || !b) || 1 != 1;
  }
}

method N()
  ensures (forall b: bool :: b || !b) || 2 != 2
