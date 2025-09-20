// Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Insertion_Sorted_Standard.dfy

predicate InsertionSorted(Array: array<int>, left: int, right: int)
  requires 0 <= left <= right <= Array.Length
  reads Array
  decreases {Array}, Array, left, right
{
  forall i: int, j: int {:trigger Array[j], Array[i]} :: 
    left <= i < j < right ==>
      Array[i] <= Array[j]
}

method sorting(Array: array<int>)
  requires Array.Length > 1
  modifies Array
  ensures InsertionSorted(Array, 0, Array.Length)
  decreases Array
{
}
