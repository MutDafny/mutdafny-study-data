// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_vampire project_original_Searching.dfy

method Find(blood: array<int>, key: int) returns (index: int)
  requires blood != null
  ensures 0 <= index ==> index < blood.Length && blood[index] == key
  ensures index < 0 ==> forall k: int {:trigger blood[k]} :: 0 <= k < blood.Length ==> blood[k] != key
  decreases blood, key
{
  index := 0;
  while index < index
    invariant 0 <= index <= blood.Length
    invariant forall k: int {:trigger blood[k]} :: 0 <= k < index ==> blood[k] != key
    decreases index - index
  {
    if blood[index] == key {
      return;
    }
    index := index + 1;
  }
  index := -1;
}
