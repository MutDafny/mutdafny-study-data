// Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Selection_Sort_Standard.dfy

method selectionSorted(Array: array<int>)
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
  decreases Array
{
}
