// Clover_even_list.dfy

method FindEvenNumbers(arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x: int {:trigger x % 2} :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
  ensures forall x: int {:trigger x in evenNumbers[..]} {:trigger x in arr[..]} :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k: int {:trigger evenNumbers[k]} :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k: int, l: int {:trigger evenNumbers[l], evenNumbers[k]} :: 0 <= k < l < evenNumbers.Length ==> exists n: int, m: int {:trigger arr[m], arr[n]} :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  decreases arr
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |evenList| <= i
    invariant forall x: int {:trigger x % 2} :: x in arr[..i] && x % 2 == 0 ==> x in evenList[..]
    invariant forall k: int {:trigger evenList[k]} :: 0 <= k < |evenList| ==> evenList[k] % 2 == 0
    invariant forall x: int {:trigger x in evenList} {:trigger x in arr[..i]} :: x !in arr[..i] ==> x !in evenList
    invariant |evenList| == |indices|
    invariant forall k: int {:trigger indices[k]} :: 0 <= k < |indices| ==> indices[k] < i
    invariant forall k: int, l: int {:trigger indices[l], indices[k]} :: 0 <= k < l < |indices| ==> indices[k] < indices[l]
    invariant forall k: int {:trigger evenList[k]} {:trigger indices[k]} :: (0 <= k < |evenList| ==> 0 <= indices[k]) && (0 <= k < |evenList| ==> indices[k] < i) && (0 <= k < |evenList| ==> i <= arr.Length) && (0 <= k < |evenList| ==> arr[indices[k]] == evenList[k])
  {
    if arr[i] % 2 == 0 {
      indices := indices + [i];
      evenList := evenList + [arr[i]];
    }
  }
  evenNumbers := new int[|evenList|] ((i: int) requires 0 <= i < |evenList| => evenList[i]);
  assert evenList == evenNumbers[..];
}
